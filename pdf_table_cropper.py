import csv
import difflib
import hashlib
import os
import re
import sys
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk

import pandas as pd
import pdfplumber
from PIL import ImageTk

GAP = 14            # space between pages (pixels)
BASE = 96 / 72      # pixels per PDF point at zoom 1.0
MIN_ZOOM, MAX_ZOOM = 0.3, 4.0


# --- smart-begin -------------------------------------------------------
import bisect
import statistics


def _text_lines(ws):
    """Words -> list of text lines (top to bottom, words left to right)."""
    ws = sorted(ws, key=lambda w: (w["top"], w["x0"]))
    lines = []
    for w in ws:
        h = w["bottom"] - w["top"]
        if lines and abs(w["top"] - lines[-1][0]) <= 0.5 * h:
            lines[-1][1].append(w)
        else:
            lines.append([w["top"], [w]])
    return [" ".join(x["text"] for x in sorted(l[1], key=lambda x: x["x0"])) for l in lines]


def _join_words(ws):
    """Join words in reading order (top to bottom, left to right)."""
    return " ".join(_text_lines(ws))


def _assign_rows(page, col, labels, ys):
    """For one merged column: which label owns each data row?
    Uses the cell edges (rect/line borders) when they give a clean answer,
    otherwise the label whose centre is nearest to the row."""
    xm = (col[0] + col[1]) / 2
    edges = []
    for r in page.rects:
        if r["x0"] <= xm <= r["x1"]:
            edges += [r["top"], r["bottom"]]
    for l in page.lines:
        if abs(l["top"] - l["bottom"]) < 1 and l["x0"] <= xm <= l["x1"]:
            edges.append(l["top"])
    if edges:
        owners = []
        for y in ys:
            hit = []
            for i, (cy, _) in enumerate(labels):
                lo = max([e for e in edges if e <= cy], default=-1e9)
                hi = min([e for e in edges if e >= cy], default=1e9)
                if lo - 0.5 <= y <= hi + 0.5:
                    hit.append(i)
            owners.append(hit)
        if all(len(h) == 1 for h in owners):
            return [h[0] for h in owners]
    return [min(range(len(labels)), key=lambda i: abs(labels[i][0] - y)) for y in ys]


def visible_fonts(full_page, cropped, dpi=200, thr=0.75):
    """Find which (font, size) groups are really visible on the page.
    PDFs often contain hidden text (clipped or covered by other shapes).
    Hidden text has no ink where it sits, so its font group scores low."""
    import numpy as np
    img = np.asarray(full_page.to_image(resolution=dpi).original.convert("L"),
                     dtype=np.int16)
    s = img.shape[1] / float(full_page.width)
    stats = {}
    for c in cropped.chars:
        if not c["text"].strip() or c["text"] in ".,:;'\"`-_|":
            continue
        h = c["bottom"] - c["top"]
        x0, x1 = int(c["x0"] * s), int(c["x1"] * s)
        y0, y1 = int((c["top"] + h * 0.2) * s), int((c["bottom"] - h * 0.2) * s)
        if x1 <= x0 or y1 <= y0:
            continue
        r = img[y0:y1, x0:x1]
        st = stats.setdefault((c["fontname"], round(c["size"], 1)), [0, 0])
        st[1] += 1
        if r.size and int(r.max()) - int(r.min()) >= 60:
            st[0] += 1
    keep = {k for k, (a, b) in stats.items() if a >= thr * b}
    return keep or set(stats)


def drop_hidden_text(full_page, cropped):
    keep = visible_fonts(full_page, cropped)
    return cropped.filter(
        lambda o: o.get("object_type") != "char"
        or (o.get("fontname"), round(o.get("size", 0), 1)) in keep)


def _smart_legacy(page, gap=6.0, fill=True):
    """Rebuild a table from word positions. Handles merged (row-spanning)
    cells and multi-line headers. Returns a list of rows or None."""
    words = page.extract_words(x_tolerance=2, y_tolerance=2)
    if len(words) < 4:
        return None
    for w in words:
        w["cy"] = (w["top"] + w["bottom"]) / 2

    # 1. Columns = x-ranges separated by gaps wider than `gap` points
    cols = []
    for a, b in sorted((w["x0"], w["x1"]) for w in words):
        if cols and a - cols[-1][1] < gap:
            cols[-1][1] = max(cols[-1][1], b)
        else:
            cols.append([a, b])
    n = len(cols)
    for w in words:
        cx = (w["x0"] + w["x1"]) / 2
        w["col"] = next(i for i, (a, b) in enumerate(cols) if a <= cx <= b)

    # 2. Rows come from the last column (it is rarely merged)
    ys = []
    for y in sorted(w["cy"] for w in words if w["col"] == n - 1):
        if not ys or y - ys[-1] >= 3:
            ys.append(y)
    if len(ys) < 2:
        return None
    gaps = [b - a for a, b in zip(ys, ys[1:])]
    med = statistics.median(gaps)
    h = 0
    while h < min(2, len(gaps) - 1) and gaps[h] < 0.8 * med:
        h += 1                       # extra header lines in the last column
    d = ys[h + 1:]                   # y of every data row
    if not d:
        return None
    R = len(d)
    bounds = [(ys[h] + d[0]) / 2] + [(d[i] + d[i + 1]) / 2 for i in range(R - 1)]

    grid = [[[] for _ in range(n)] for _ in range(R + 1)]   # grid[0] = header
    for w in words:
        grid[bisect.bisect(bounds, w["cy"])][w["col"]].append(w)

    # 3. Merged columns: left-hand columns that are not filled on every row
    cover = [sum(1 for r in grid[1:] if r[c]) for c in range(n)]
    k = next((c for c in range(n) if cover[c] == R), n)
    merged = [c for c in range(k) if cover[c] < R]

    out = [[_join_words(grid[0][c]) for c in range(n)]]
    for r in range(1, R + 1):
        out.append(["" if c in merged else _join_words(grid[r][c]) for c in range(n)])

    for c in merged:
        ws = sorted((w for r in grid[1:] for w in r[c]), key=lambda w: w["cy"])
        groups = []
        for w in ws:
            limit = min(1.35 * (w["bottom"] - w["top"]), 0.9 * med)
            if groups and w["cy"] - groups[-1][-1]["cy"] <= limit:
                groups[-1].append(w)
            else:
                groups.append([w])
        labels = [(sum(w["cy"] for w in g) / len(g), _join_words(g)) for g in groups]
        owners = _assign_rows(page, cols[c], labels, d)
        prev = None
        for i, o in enumerate(owners):
            if fill or o != prev:
                out[i + 1][c] = labels[o][1]
            prev = o
    return out

NUM_RE = re.compile(r"^[-+]?\d[\d,]*(\.\d+)?%?$")
CCT_RE = re.compile(r"^\d{3,4}\s*K(\s*/\s*\d{3,4}\s*K)?$", re.I)


LAYOUTS = ["Two-row header, titles merged (like the PDF)",
           "One row per CCT / distribution (CCT as a column)",
           "Single-row header (2700K Lumens)"]


class SmartTable(list):
    """Rows of a table, plus the group / name of every column header."""
    groups = None
    names = None


def smart_table(page, gap=6.0, fill=True):
    """Rebuild a table from word positions: merged cells, multi-line headers and
    grouped headers (one title above several columns, e.g. R2 over Lumens + LPW).
    Returns a SmartTable (list of rows, header first) or None."""
    words = page.extract_words(x_tolerance=2, y_tolerance=2)
    if len(words) < 4:
        return None
    for w in words:
        w["cy"] = (w["top"] + w["bottom"]) / 2

    # 1. The header ends where the first data line (two or more numbers) begins
    lines = []
    for w in sorted(words, key=lambda w: w["cy"]):
        if lines and w["cy"] - lines[-1][-1]["cy"] <= 0.6 * (w["bottom"] - w["top"]):
            lines[-1].append(w)
        else:
            lines.append([w])
    def data_numbers(line):
        """Numbers that stand alone in their cell (not part of a title like '70 CRI')."""
        ws, count = sorted(line, key=lambda w: w["x0"]), 0
        for i, w in enumerate(ws):
            if not NUM_RE.match(w["text"]):
                continue
            left = w["x0"] - ws[i - 1]["x1"] if i > 0 else 99
            right = ws[i + 1]["x0"] - w["x1"] if i < len(ws) - 1 else 99
            if left >= 5 and right >= 5:
                count += 1
        return count

    first = next((l for l in lines if data_numbers(l) >= 2), None)
    if first is None:
        return _smart_legacy(page, gap, fill)
    cut = min(w["top"] for w in first) - 0.5
    head = [w for w in words if w["cy"] < cut]
    body = [w for w in words if w["cy"] >= cut]
    if not head:
        return _smart_legacy(page, gap, fill)

    # 2. Columns come from the data only (a spanning header must not merge columns)
    cols = []
    for a, b in sorted((w["x0"], w["x1"]) for w in body):
        if cols and a - cols[-1][1] < gap:
            cols[-1][1] = max(cols[-1][1], b)
        else:
            cols.append([a, b])
    n = len(cols)
    for w in body:
        cx = (w["x0"] + w["x1"]) / 2
        w["col"] = next(i for i, (a, b) in enumerate(cols) if a <= cx <= b)
    edges = [-1e9] + [(cols[i][1] + cols[i + 1][0]) / 2 for i in range(n - 1)] + [1e9]

    # 3. Data rows come from the column with the most rows (a number column that is
    #    filled on every row), never from a merged column such as the last one
    def row_ys(c):
        ys = []
        for y in sorted(w["cy"] for w in body if w["col"] == c):
            if not ys or y - ys[-1] >= 3:
                ys.append(y)
        return ys

    def numeric_share(c):
        ws = [w for w in body if w["col"] == c]
        return sum(1 for w in ws if NUM_RE.match(w["text"])) / max(1, len(ws))

    numeric_cols = [c for c in range(n) if numeric_share(c) >= 0.6] or list(range(n))
    d = max((row_ys(c) for c in numeric_cols), key=len)
    if len(d) < 2:
        return _smart_legacy(page, gap, fill)
    R = len(d)
    med = statistics.median(b - a for a, b in zip(d, d[1:]))
    bounds = [(d[i] + d[i + 1]) / 2 for i in range(R - 1)]
    grid = [[[] for _ in range(n)] for _ in range(R)]
    for w in body:
        grid[bisect.bisect(bounds, w["cy"])][w["col"]].append(w)

    # 4. Header: a title whose cell covers several columns is a group title (R2, R3 ...).
    #    The cell borders (vertical lines) tell how wide a header cell is.
    vedges = [e for e in page.edges if e.get("orientation") == "v"]
    ccent = [(a + b) / 2 for a, b in cols]
    spans = [[] for _ in range(n)]
    under = [[] for _ in range(n)]
    for w in head:
        ov = [max(0.0, min(w["x1"], edges[i + 1]) - max(w["x0"], edges[i])) for i in range(n)]
        wid = max(w["x1"] - w["x0"], 1e-6)
        cx = (w["x0"] + w["x1"]) / 2
        hit = None
        near = [e["x0"] for e in vedges if e["top"] - 1 <= w["cy"] <= e["bottom"] + 1]
        left = max((x for x in near if x <= cx - 0.5), default=None)
        right = min((x for x in near if x >= cx + 0.5), default=None)
        if left is not None and right is not None:
            inside = [i for i in range(n) if left < ccent[i] < right]
            if inside and not (n > 3 and len(inside) > n / 2):
                hit = inside
        if hit is None:                              # no usable borders: use overlap
            hit = [i for i, o in enumerate(ov) if o >= 0.25 * wid]
        if len(hit) >= 2:
            for i in hit:
                spans[i].append(w)
        else:
            under[hit[0] if hit else max(range(n), key=lambda i: ov[i])].append(w)
    group, names = [], []
    for i in range(n):
        g = _join_words(spans[i])
        lines_i = _text_lines(under[i])
        if not g:                                   # e.g. 2700K above "Lumens"
            for ln in lines_i:
                if CCT_RE.match(ln):
                    g = ln
                    lines_i.remove(ln)
                    break
        group.append(g)
        names.append(" ".join(lines_i))
    # without cell borders a CCT title is found over one column only: carry it to the
    # untitled number columns on its right (2700K over Lumens -> also over LPW)
    for i in range(1, n):
        if not group[i] and group[i - 1] and variant_of(group[i - 1]) \
                and names[i] and numeric_share(i) >= 0.6:
            group[i] = group[i - 1]
    header = [" ".join(x for x in (group[i], names[i]) if x) for i in range(n)]

    # 5. Body cells; merged columns repeat their label on every row they cover
    body_rows = [[_join_words(grid[r][c]) for c in range(n)] for r in range(R)]
    cover = [sum(1 for r in grid if r[c]) for c in range(n)]
    k = next((c for c in range(n) if cover[c] == R), n)

    def labels_of(c):
        ws = sorted((w for r in grid for w in r[c]), key=lambda w: w["cy"])
        groups = []
        for w in ws:
            limit = min(1.35 * (w["bottom"] - w["top"]), 0.9 * med)
            if groups and w["cy"] - groups[-1][-1]["cy"] <= limit:
                groups[-1].append(w)
            else:
                groups.append([w])
        return [(sum(w["cy"] for w in g) / len(g), _join_words(g)) for g in groups]

    def put(c, labels, owners):
        prev = None
        for i, o in enumerate(owners):
            body_rows[i][c] = labels[o][1] if (fill or o != prev) else ""
            prev = o

    seed_owner, seed_count = None, None
    for c in range(k):                              # left-hand columns with blanks
        if cover[c] < R:
            labels = labels_of(c)
            owners = _assign_rows(page, cols[c], labels, d)
            put(c, labels, owners)
            if seed_owner is None:
                seed_owner, seed_count = owners, len(labels)
    if seed_owner:                                  # other columns merged the same way
        for c in range(k, n):
            if 0 < cover[c] < R:
                labels = labels_of(c)
                if len(labels) == seed_count:
                    put(c, labels, seed_owner)

    res = SmartTable([header] + body_rows)
    res.groups, res.names = group, names
    return res


TOKEN_RE = re.compile(r"\d{3,4}\s*K(?:\s*/\s*\d{3,4}\s*K)?", re.I)


def variant_of(title):
    """The CCT (2700K, 4000K/5000K) or distribution (R2) hidden in a group title."""
    t = title.strip()
    if re.fullmatch(r"R\d+", t, re.I):
        return t.upper()
    m = TOKEN_RE.search(t)
    return re.sub(r"\s+", "", m.group(0)).upper() if m else ""


def reshape_long(rows, groups, names, new_name=""):
    """Turn column groups into rows.
      R2 / R3 / R4 / R5 over Lumens + LPW            -> a 'Distribution' column
      2700K / 3000K over Lumens                      -> a 'CCT' column
      '3K (3000K CCT, 70 CRI)' over Lumens, LPW, B.. -> a 'CCT' column with 3000K
    Other columns (Package, Watts, 'LLD @ 25C' ...) are repeated on every new row.
    Rows with no values at all (only '-') are dropped."""
    if not groups or not any(groups):
        return rows
    n = len(rows[0])
    var = [variant_of(g) if g else "" for g in groups]
    order = []
    for v in var:
        if v and v not in order:
            order.append(v)
    if len(order) < 2:
        return rows
    ids = [c for c in range(n) if not var[c]]
    vnames = []
    for c in range(n):
        if var[c]:
            nm = names[c] or "Value"
            if nm not in vnames:
                vnames.append(nm)
    if not new_name:
        if all(TOKEN_RE.fullmatch(v) for v in order):
            new_name = "CCT"
        elif all(re.fullmatch(r"R\d+", v) for v in order):
            new_name = "Distribution"
        else:
            new_name = "Group"
    pos = {(var[c], names[c] or "Value"): c for c in range(n) if var[c]}
    blank = lambda v: v.strip() in ("", "-", "\u2013", "\u2014")
    out = [[rows[0][c] for c in ids] + [new_name] + vnames]
    for r in rows[1:]:
        for v in order:
            vals = [r[pos[(v, nm)]] if (v, nm) in pos else "" for nm in vnames]
            if all(blank(x) for x in vals):
                continue
            out.append([r[c] for c in ids] + [v] + vals)
    return out
DEFAULT_KEYWORDS = "Lumens, Lumen, LPW, Watts, Wattage, CCT, Distribution, Package, Efficacy, Delivered"


def _cluster_lines(words):
    """Words -> text lines, top to bottom."""
    lines = []
    for w in sorted(words, key=lambda w: w["cy"]):
        if lines and w["cy"] - lines[-1]["cy"] <= 0.6 * (w["bottom"] - w["top"]):
            ln = lines[-1]
            ln["words"].append(w)
            ln["cy"] = sum(x["cy"] for x in ln["words"]) / len(ln["words"])
        else:
            lines.append({"words": [w], "cy": w["cy"]})
    for ln in lines:
        ln["words"].sort(key=lambda w: w["x0"])
        ln["top"] = min(w["top"] for w in ln["words"])
        ln["bottom"] = max(w["bottom"] for w in ln["words"])
        ln["h"] = sum(w["bottom"] - w["top"] for w in ln["words"]) / len(ln["words"])
    return lines


def find_performance_tables(page, keywords, min_hits=3):
    """Look for tables whose header holds at least `min_hits` of the given words
    (Lumens, LPW, Watts, CCT ...) and that have number rows underneath.
    Returns [{'bbox': (x0, top, x1, bottom), 'rows': n, 'hits': [...]}] top to bottom."""
    kw = {re.sub(r"[^a-z0-9]", "", k.lower()) for k in keywords}
    kw.discard("")
    words = page.extract_words(x_tolerance=2, y_tolerance=2)
    if len(words) < 8 or not kw:
        return []
    for w in words:
        w["cy"] = (w["top"] + w["bottom"]) / 2
    lines = _cluster_lines(words)

    def hits_of(ln):
        return {re.sub(r"[^a-z0-9]", "", w["text"].lower()) for w in ln["words"]} & kw

    def header_like(ln):                       # prose has many lower-case words
        toks = [w["text"] for w in ln["words"]]
        lower = sum(1 for t in toks if t[:1].islower())
        return len(toks) <= 24 and lower <= 0.3 * len(toks)

    kw_idx = [i for i, ln in enumerate(lines) if hits_of(ln) and header_like(ln)]
    # header blocks: keyword lines that sit close together
    blocks, cur = [], []
    for i in kw_idx:
        if cur and lines[i]["top"] - lines[cur[-1]]["bottom"] > max(16.0, 2.5 * lines[i]["h"]):
            blocks.append(cur)
            cur = []
        cur.append(i)
    if cur:
        blocks.append(cur)

    found, limit_y = [], -1.0
    for blk in blocks:
        lo, hi = blk[0], blk[-1]
        block_hits = set()
        for i in range(lo, hi + 1):
            block_hits |= hits_of(lines[i])
        if len(block_hits) < min_hits or lines[lo]["top"] < limit_y:
            continue
        # title lines just above the header (2700K, R2 ...)
        while lo > 0:
            prev = lines[lo - 1]
            titles = [w["text"] for w in prev["words"]]
            if (lines[lo]["top"] - prev["bottom"] <= 1.8 * lines[lo]["h"]
                    and titles and all(variant_of(t) for t in titles)):
                lo -= 1
            else:
                break
        hdr_words = [w for i in range(lo, hi + 1) for w in lines[i]["words"]]
        hx0 = min(w["x0"] for w in hdr_words)
        hx1 = max(w["x1"] for w in hdr_words)
        hdr_bottom = lines[hi]["bottom"]
        # a header cell can have a second text line (25k / Hours): it still belongs to the header
        under = _cluster_lines([w for w in words if w["top"] >= hdr_bottom - 1
                                and hx0 - 20 <= (w["x0"] + w["x1"]) / 2 <= hx1 + 20])
        for ln in under:
            if (all(re.fullmatch(r"[A-Za-z][A-Za-z.,:;'()/\-]{2,}", w["text"]) for w in ln["words"])
                    and ln["top"] - hdr_bottom <= 1.6 * ln["h"]):
                hdr_bottom = ln["bottom"]
            else:
                break
        # rows below the header: only words standing over the header's columns
        near = [w for w in words if w["top"] >= hdr_bottom - 1
                and hx0 - 20 <= (w["x0"] + w["x1"]) / 2 <= hx1 + 20]
        below = _cluster_lines(near)
        body, prev, gaps, number_lines = [], None, [], 0
        for ln in below:
            toks = [w["text"] for w in ln["words"]]
            nums = sum(1 for t in toks if NUM_RE.match(t))
            alpha = sum(1 for t in toks if re.fullmatch(r"[A-Za-z][A-Za-z.,:;'()/\-]{2,}", t))
            sentence = nums == 0 and len(toks) >= 3 and alpha >= 0.6 * len(toks)
            gap = ln["top"] - (prev["bottom"] if prev else hdr_bottom)
            limit = max(12.0, 2.5 * statistics.median(gaps)) if len(gaps) >= 3 else 14.0
            if sentence or gap > limit or len(hits_of(ln)) >= 2:
                break
            body.append(ln)
            number_lines += 1 if nums else 0
            gaps.append(max(gap, 0.0))
            prev = ln
        if number_lines < 3:
            continue
        xs0 = min([hx0] + [w["x0"] for ln in body for w in ln["words"]])
        xs1 = max([hx1] + [w["x1"] for ln in body for w in ln["words"]])
        top, bottom = lines[lo]["top"], body[-1]["bottom"]
        found.append({"bbox": (max(0.0, xs0 - 4), max(0.0, top - 3),
                               min(float(page.width), xs1 + 4), min(float(page.height), bottom + 3)),
                      "rows": number_lines, "hits": sorted(block_hits)})
        limit_y = bottom
    return found
# --- smart-end ---------------------------------------------------------


# --- csv-target-begin --------------------------------------------------
def _norm(text):
    return re.sub(r"[^a-z0-9]", "", str(text).lower())


def unique_names(names):
    out, used = [], {}
    for i, value in enumerate(names):
        name = str(value).strip() or f"Column_{i + 1}"
        if name in used:
            used[name] += 1
            name = f"{name}_{used[name]}"
        else:
            used[name] = 1
        out.append(name)
    return out


def auto_match(template, extracted):
    """For every column of the target CSV, pick the best extracted column
    (index) or None. Exact name first, then similar names."""
    ex = [_norm(c) for c in extracted]
    result, used = [None] * len(template), set()
    for i, t in enumerate(template):                 # pass 1: same name
        tn = _norm(t)
        for j, e in enumerate(ex):
            if tn and e == tn and j not in used:
                result[i] = j
                used.add(j)
                break
    for i, t in enumerate(template):                 # pass 2: similar name
        if result[i] is not None:
            continue
        tn, best, score = _norm(t), None, 0.0
        for j, e in enumerate(ex):
            if j in used or not e or not tn:
                continue
            r = difflib.SequenceMatcher(None, tn, e).ratio()
            if (tn in e or e in tn) and min(len(tn), len(e)) >= 3:
                r = max(r, 0.85)
            if r > score:
                best, score = j, r
        if best is not None and score >= 0.7:
            result[i] = best
            used.add(best)
    return result


def read_csv_header(path):
    """Return (column names, encoding) of a CSV. ([], 'utf-8-sig') if missing/empty."""
    if not path or not os.path.isfile(path) or os.path.getsize(path) == 0:
        return [], "utf-8-sig"
    for enc in ("utf-8-sig", "cp1252", "latin-1"):
        try:
            with open(path, newline="", encoding=enc) as f:
                row = next(csv.reader(f), [])
            return [c.strip() for c in row], enc
        except UnicodeDecodeError:
            continue
    return [], "utf-8-sig"


def write_header(path, cols):
    """Create the CSV with these columns, or replace the header of an existing one."""
    _, enc = read_csv_header(path)
    rows = []
    if os.path.isfile(path) and os.path.getsize(path) > 0:
        with open(path, newline="", encoding=enc) as f:
            rows = list(csv.reader(f))
    if rows:
        rows[0] = list(cols)
    else:
        rows = [list(cols)]
    with open(path, "w", newline="", encoding=enc) as f:
        csv.writer(f).writerows(rows)


def append_rows(path, rows, header=None):
    """Add rows to the end of the CSV (writes `header` first if the file is new)."""
    cols, enc = read_csv_header(path)
    new = not cols
    needs_newline = False
    if not new:
        with open(path, "rb") as b:
            b.seek(-1, os.SEEK_END)
            needs_newline = b.read(1) not in (b"\n", b"\r")
    with open(path, "a", newline="", encoding=enc) as f:
        if needs_newline:
            f.write("\r\n")
        w = csv.writer(f)
        if new and header:
            w.writerow(header)
        w.writerows(rows)


def is_excel(path):
    return str(path).lower().endswith((".xlsx", ".xlsm"))


def sheet_name_for(pdf_path, suffix=""):
    """Excel tab name for a PDF: its file name (no .pdf), made valid for Excel.
    `suffix` (for example ' (2)') marks a second table type of the same PDF."""
    base = os.path.splitext(os.path.basename(pdf_path or ""))[0]
    name = re.sub(r"[\[\]:*?/\\]", "_", base).strip("'") or "Sheet"
    room = 31 - len(suffix)
    if len(name) > room:               # Excel limit; add a short stable suffix
        name = name[:room - 4] + "_" + hashlib.md5(base.encode("utf-8")).hexdigest()[:3]
    return name + suffix


_LAYOUT_CACHE = {}


def read_xlsx_layout(path):
    """(flat column names, groups, names) of the first sheet of a workbook.
    groups / names are None for an ordinary one-row header; for a two-row header with
    merged titles they list the title above every column and the name under it."""
    if not path or not os.path.isfile(path):
        return [], None, None
    stamp = (path, os.path.getmtime(path))
    if stamp in _LAYOUT_CACHE:
        return _LAYOUT_CACHE[stamp]
    from openpyxl import load_workbook
    wb = load_workbook(path)
    try:
        ws = wb[wb.sheetnames[0]]
        ncol = ws.max_column or 0
        val = lambda r, c: "" if ws.cell(r, c).value is None else str(ws.cell(r, c).value).strip()
        spans = [g for g in ws.merged_cells.ranges
                 if g.min_row == 1 and g.max_row == 1 and g.max_col > g.min_col]
        if not spans or (ws.max_row or 0) < 2:
            row = [val(1, c) for c in range(1, ncol + 1)]
            while row and not row[-1]:
                row.pop()
            result = (row, None, None)
        else:
            groups, names = [], []
            for c in range(1, ncol + 1):
                g = next((val(1, r.min_col) for r in spans if r.min_col <= c <= r.max_col), "")
                groups.append(g)
                names.append(val(2, c) if g else (val(1, c) or val(2, c)))
            flat = [" ".join(x for x in (g, nm) if x) for g, nm in zip(groups, names)]
            result = (flat, groups, names)
    finally:
        wb.close()
    _LAYOUT_CACHE.clear()
    _LAYOUT_CACHE[stamp] = result
    return result


def read_xlsx_header(path):
    """Column names of the first sheet ([] if missing or empty)."""
    return read_xlsx_layout(path)[0]


def _excel_value(v):
    """Store plain numbers as numbers (not text); keep codes like 007 as text."""
    if isinstance(v, str):
        if re.fullmatch(r"-?(0|[1-9]\d*)(\.\d+)?", v):
            return float(v) if "." in v else int(v)
        if re.fullmatch(r"-?\d{1,3}(,\d{3})+(\.\d+)?", v):        # 11,911  ->  11911
            v = v.replace(",", "")
            return float(v) if "." in v else int(v)
    return v


def sheet_exists(path, sheet):
    from openpyxl import load_workbook
    wb = load_workbook(path, read_only=True)
    try:
        return any(n.lower() == sheet.lower() for n in wb.sheetnames)
    finally:
        wb.close()


def two_row_header(groups, names):
    """(top row, second row) for a header whose titles span several columns."""
    top, second = [], []
    for c, g in enumerate(groups):
        if g:
            top.append(g if c == 0 or groups[c - 1] != g else "")
            second.append(names[c])
        else:
            top.append(names[c])
            second.append("")
    return top, second


def _write_two_row_header(ws, groups, names):
    """Titles merged over their columns (like the PDF); other columns merged downwards."""
    from openpyxl.styles import Alignment, Border, Font, PatternFill, Side
    top, second = two_row_header(groups, names)
    ws.append(top)
    ws.append(second)
    n = len(groups)
    c = 0
    while c < n:
        if groups[c]:
            e = c
            while e + 1 < n and groups[e + 1] == groups[c]:
                e += 1
            if e > c:
                ws.merge_cells(start_row=1, end_row=1, start_column=c + 1, end_column=e + 1)
            c = e + 1
        else:
            ws.merge_cells(start_row=1, end_row=2, start_column=c + 1, end_column=c + 1)
            c += 1
    side = Side(style="thin", color="999999")
    for r in (1, 2):
        for col in range(1, n + 1):
            cell = ws.cell(r, col)
            cell.font = Font(bold=True)
            cell.alignment = Alignment(horizontal="center", vertical="center", wrap_text=True)
            cell.fill = PatternFill("solid", fgColor="DDE3EA")
            cell.border = Border(left=side, right=side, top=side, bottom=side)
    ws.freeze_panes = "A3"


def append_xlsx(path, sheet, rows, header, meta=None):
    """Add rows to the tab `sheet` of the workbook (tab and file are created if needed).
    meta = (groups, names) writes a two-row header with merged titles on a new tab."""
    from openpyxl import Workbook, load_workbook
    if os.path.isfile(path):
        wb = load_workbook(path)
    else:
        wb = Workbook()
        wb.remove(wb.active)
    found = next((n for n in wb.sheetnames if n.lower() == sheet.lower()), None)
    ws = wb[found] if found else wb.create_sheet(sheet)
    if not ws._cells and header:       # brand-new (empty) tab: write the header first
        if meta and meta[0] and any(meta[0]) and len(meta[0]) == len(header):
            _write_two_row_header(ws, meta[0], meta[1])
        else:
            ws.append(list(header))
    for r in rows:
        ws.append([_excel_value(v) for v in r])
        for cell, v in zip(ws[ws.max_row], r):       # keep the thousands separator
            if isinstance(v, str) and "," in v and isinstance(cell.value, (int, float)):
                dec = len(v.split(".")[1]) if "." in v else 0
                cell.number_format = "#,##0" + ("." + "0" * dec if dec else "")
    wb.save(path)
    return ws.title
# --- csv-target-end ----------------------------------------------------


class PDFTableCropper:
    def __init__(self, root):
        self.root = root
        self.root.title("PDF Table Cropper to CSV")
        self.root.geometry("1350x850")

        self.pdf = None
        self.pdf_path = None
        self.sizes = []          # (width, height) of every page in PDF points
        self.boxes = []          # (x, y, w, h) of every page on the canvas
        self.images = {}         # page index -> (PhotoImage, canvas item id)
        self.zoom = 1.0
        self.render_job = None

        self.rect_id = None
        self.start_x = None
        self.start_y = None
        self.drag_page = None
        self.panning = False
        self.edit = None         # box being resized / moved: {idx, mode, sx, sy, bbox}
        # every selected table: {"page": index, "bbox": (left, top, right, bottom) in PDF points}
        self.selections = []
        self.df = None
        self.folder_files = []   # PDFs of the loaded folder
        self.folder_index = 0
        self.mapping_memory = {}   # remembered column matching
        self.xlsx_cols = {}        # predefined columns for Excel targets: path -> [names]
        self.xlsx_meta = {}        # two-row header of Excel targets: path -> (groups, names)
        self.header_meta = None    # (groups, names) of the combined table, if grouped
        self.df_meta = None
        self.sheet_suffix = ""     # ' (2)' for a second table type of the same PDF
        self.own_header = False    # second table type: keep its own columns, no template
        self.batch_log = []        # notes collected while a folder runs automatically
        self.last_load_ok = None
        self.raw_df = None         # extracted table before column edits
        self.raw_meta = None
        self.edits = {}            # column edits: original name -> ("delete",) / ("rename", text)
        self.col_origin = []       # original name of every column shown in the preview
        self.sel_col = None        # column picked in the preview
        self.loaded_key = None     # what was loaded into the target CSV last

        self.build_gui()

    # --------------------------------------------------
    # GUI
    # --------------------------------------------------
    def build_gui(self):
        toolbar = ttk.Frame(self.root, padding=8)
        toolbar.pack(fill="x")

        ttk.Button(toolbar, text="Open PDF", command=self.open_pdf).pack(side="left", padx=4)

        ttk.Label(toolbar, text="Page:").pack(side="left", padx=(12, 3))
        self.page_var = tk.StringVar(value="1")
        entry = ttk.Entry(toolbar, textvariable=self.page_var, width=5)
        entry.pack(side="left")
        entry.bind("<Return>", lambda e: self.go_to_page())
        ttk.Button(toolbar, text="Go", command=self.go_to_page).pack(side="left", padx=4)
        self.page_count = tk.StringVar(value="/ 0")
        ttk.Label(toolbar, textvariable=self.page_count).pack(side="left")

        # Zoom controls
        ttk.Separator(toolbar, orient="vertical").pack(side="left", fill="y", padx=10)
        ttk.Button(toolbar, text="Zoom -", width=7,
                   command=lambda: self.zoom_by(1 / 1.25)).pack(side="left", padx=2)
        self.zoom_label = tk.StringVar(value="100%")
        ttk.Label(toolbar, textvariable=self.zoom_label, width=6,
                  anchor="center").pack(side="left")
        ttk.Button(toolbar, text="Zoom +", width=7,
                   command=lambda: self.zoom_by(1.25)).pack(side="left", padx=2)
        ttk.Button(toolbar, text="Fit Width", command=self.fit_width).pack(side="left", padx=4)
        self.hand_mode = tk.BooleanVar(value=False)
        ttk.Checkbutton(toolbar, text="Hand (move PDF)", variable=self.hand_mode,
                        style="Toolbutton",
                        command=self.update_cursor).pack(side="left", padx=4)
        ttk.Separator(toolbar, orient="vertical").pack(side="left", fill="y", padx=10)

        ttk.Button(toolbar, text="Auto-Find Tables", command=self.auto_find_tables).pack(side="left", padx=4)
        ttk.Button(toolbar, text="Undo Last", command=self.undo_selection).pack(side="left", padx=4)
        ttk.Button(toolbar, text="Clear All", command=self.clear_selection).pack(side="left", padx=4)
        ttk.Button(toolbar, text="Extract Tables", command=self.extract_table).pack(side="left", padx=4)
        ttk.Button(toolbar, text="Extract + Save CSV", command=self.extract_and_save).pack(side="left", padx=4)
        ttk.Button(toolbar, text="Save CSV", command=self.save_csv).pack(side="left", padx=4)

        # Folder bar: load a folder, then step through its PDFs one by one
        bar = ttk.Frame(self.root, padding=(8, 0, 8, 6))
        bar.pack(fill="x")
        ttk.Label(bar, text="PDF folder:").pack(side="left")
        self.folder_var = tk.StringVar()
        folder_entry = ttk.Entry(bar, textvariable=self.folder_var)
        folder_entry.pack(side="left", fill="x", expand=True, padx=6)
        folder_entry.bind("<Return>", lambda e: self.load_folder())
        ttk.Button(bar, text="Browse", command=self.browse_folder).pack(side="left", padx=2)
        ttk.Button(bar, text="Load Folder", command=self.load_folder).pack(side="left", padx=2)
        ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=8)
        ttk.Button(bar, text="< Prev PDF",
                   command=lambda: self.step_pdf(-1)).pack(side="left", padx=2)
        self.pdf_counter = tk.StringVar(value="No folder loaded")
        ttk.Label(bar, textvariable=self.pdf_counter, width=36,
                  anchor="center").pack(side="left")
        ttk.Button(bar, text="Next PDF >",
                   command=lambda: self.step_pdf(1)).pack(side="left", padx=2)
        ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=8)
        ttk.Button(bar, text="Run Folder Automatically",
                   command=self.run_folder_auto).pack(side="left", padx=2)

        # Target CSV bar: predefined columns + where extracted data is loaded
        tbar = ttk.Frame(self.root, padding=(8, 0, 8, 0))
        tbar.pack(fill="x")
        ttk.Label(tbar, text="Target file:").pack(side="left")
        self.target_var = tk.StringVar()
        target_entry = ttk.Entry(tbar, textvariable=self.target_var)
        target_entry.pack(side="left", fill="x", expand=True, padx=6)
        target_entry.bind("<Return>", lambda e: self.apply_target())
        target_entry.bind("<FocusOut>", lambda e: self.refresh_target())
        ttk.Button(tbar, text="Choose / Create...",
                   command=self.choose_target).pack(side="left", padx=2)
        ttk.Button(tbar, text="Set Columns...",
                   command=self.set_columns).pack(side="left", padx=2)
        self.confirm_always = tk.BooleanVar(value=False)
        ttk.Checkbutton(tbar, text="Confirm matching every time",
                        variable=self.confirm_always).pack(side="left", padx=8)
        self.auto_sheet = tk.BooleanVar(value=True)
        ttk.Checkbutton(tbar, text="New tab when a PDF opens (.xlsx)",
                        variable=self.auto_sheet).pack(side="left", padx=8)
        self.target_info = tk.StringVar(
            value="No target file. Extracted tables will be saved with Save CSV.")
        ttk.Label(self.root, textvariable=self.target_info, padding=(10, 0, 10, 4),
                  foreground="#555").pack(fill="x")

        self.status = tk.StringVar(value="Open a PDF to begin.")
        ttk.Label(self.root, textvariable=self.status, padding=(10, 4)).pack(fill="x")

        main = ttk.PanedWindow(self.root, orient="horizontal")
        main.pack(fill="both", expand=True, padx=8, pady=8)

        left = ttk.Frame(main)
        right = ttk.Frame(main)
        main.add(left, weight=3)
        main.add(right, weight=2)

        # PDF canvas (all pages stacked, scrollable)
        self.canvas = tk.Canvas(left, background="#8a8f98", cursor="crosshair",
                                highlightthickness=0)
        self.scroll_y = ttk.Scrollbar(left, orient="vertical", command=self.canvas.yview)
        self.scroll_x = ttk.Scrollbar(left, orient="horizontal", command=self.canvas.xview)
        self.canvas.configure(yscrollcommand=self._yscroll, xscrollcommand=self.scroll_x.set)

        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.scroll_y.grid(row=0, column=1, sticky="ns")
        self.scroll_x.grid(row=1, column=0, sticky="ew")
        left.rowconfigure(0, weight=1)
        left.columnconfigure(0, weight=1)

        self.canvas.bind("<ButtonPress-1>", self.start_crop)
        self.canvas.bind("<B1-Motion>", self.move_crop)
        self.canvas.bind("<ButtonRelease-1>", self.finish_crop)
        if sys.platform == "darwin":
            self.canvas.bind("<Button-2>", self.remove_at)           # right-click
            self.canvas.bind("<Control-Button-1>", self.remove_at)
        else:
            self.canvas.bind("<Button-3>", self.remove_at)           # right-click removes a box
            # Middle mouse button: always drag the PDF around
            self.canvas.bind("<ButtonPress-2>", self.pan_start)
            self.canvas.bind("<B2-Motion>", self.pan_move)
            self.canvas.bind("<ButtonRelease-2>", self.pan_end)
        self.canvas.bind("<Motion>", self.on_motion)
        self.canvas.bind("<Configure>", lambda e: self.schedule_render())
        self.canvas.bind("<Enter>", lambda e: self.canvas.focus_set())

        # Mouse wheel: scroll, Shift = horizontal, Ctrl = zoom
        self.canvas.bind("<MouseWheel>", self.on_wheel)
        self.canvas.bind("<Button-4>", self.on_wheel)   # Linux
        self.canvas.bind("<Button-5>", self.on_wheel)   # Linux

        # Keyboard zoom
        self.root.bind("<Control-plus>", lambda e: self.zoom_by(1.25))
        self.root.bind("<Control-equal>", lambda e: self.zoom_by(1.25))
        self.root.bind("<Control-minus>", lambda e: self.zoom_by(1 / 1.25))
        self.root.bind("<Control-0>", lambda e: self.fit_width())

        # Extraction settings + preview
        ttk.Label(right, text="Extraction method:").pack(anchor="w", padx=5, pady=(5, 2))
        self.method = tk.StringVar(value="Smart (merged cells)")
        ttk.Combobox(right, textvariable=self.method,
                     values=["Smart (merged cells)", "Automatic", "Lines", "Text"],
                     state="readonly").pack(fill="x", padx=5, pady=(0, 8))

        gap_row = ttk.Frame(right)
        gap_row.pack(anchor="w", padx=5, pady=(0, 6))
        ttk.Label(gap_row, text="Column gap (pt, Smart mode):").pack(side="left")
        self.col_gap = tk.DoubleVar(value=6)
        ttk.Spinbox(gap_row, from_=1, to=40, increment=1, width=5,
                    textvariable=self.col_gap).pack(side="left", padx=6)

        auto_box = ttk.LabelFrame(right, text="Automatic table search", padding=6)
        auto_box.pack(fill="x", padx=5, pady=(0, 6))
        self.select_mode = tk.StringVar(value="auto")
        ttk.Radiobutton(auto_box, variable=self.select_mode, value="auto",
                        text="Automatic first: find the table by the header words below.\n"
                             "If none is found, I select the table myself.").pack(anchor="w")
        ttk.Radiobutton(auto_box, variable=self.select_mode, value="manual",
                        text="Manual only: I always select the table myself.").pack(anchor="w", pady=(2, 0))
        self.auto_extract = tk.BooleanVar(value=True)
        ttk.Checkbutton(auto_box, text="Extract straight away when a table is found",
                        variable=self.auto_extract).pack(anchor="w", pady=(4, 0))
        kw_row = ttk.Frame(auto_box)
        kw_row.pack(fill="x", pady=(4, 0))
        ttk.Label(kw_row, text="Header words:").pack(side="left")
        self.kw_var = tk.StringVar(value=DEFAULT_KEYWORDS)
        ttk.Entry(kw_row, textvariable=self.kw_var).pack(side="left", fill="x", expand=True, padx=4)
        multi_row = ttk.Frame(auto_box)
        multi_row.pack(fill="x", pady=(4, 0))
        ttk.Label(multi_row, text="Several table types in a PDF:").pack(side="left")
        self.multi_mode = tk.StringVar(value="Best match only")
        ttk.Combobox(multi_row, textvariable=self.multi_mode, state="readonly", width=34,
                     values=["Best match only", "All (each type on its own tab)"]
                     ).pack(side="left", padx=6)
        hit_row = ttk.Frame(auto_box)
        hit_row.pack(fill="x", pady=(4, 0))
        ttk.Label(hit_row, text="Header words needed to match:").pack(side="left")
        self.min_hits = tk.IntVar(value=3)
        ttk.Spinbox(hit_row, from_=1, to=8, width=4, textvariable=self.min_hits).pack(side="left", padx=6)

        self.skip_hidden = tk.BooleanVar(value=True)
        ttk.Checkbutton(right, text="Ignore hidden text (clipped / covered by other shapes)",
                        variable=self.skip_hidden).pack(anchor="w", padx=5, pady=(0, 4))

        self.fill_merged = tk.BooleanVar(value=True)
        ttk.Checkbutton(right, text="Fill merged cells (repeat value on every row)",
                        variable=self.fill_merged).pack(anchor="w", padx=5, pady=(0, 4))

        self.add_source = tk.BooleanVar(value=False)
        ttk.Checkbutton(right, text="Add File, Page and Table # columns to the extracted data",
                        variable=self.add_source).pack(anchor="w", padx=5, pady=(0, 4))

        ttk.Label(right, text="Table layout (tables with grouped headers):").pack(anchor="w", padx=5)
        self.table_layout = tk.StringVar(value=LAYOUTS[0])
        ttk.Combobox(right, textvariable=self.table_layout, values=LAYOUTS,
                     state="readonly").pack(fill="x", padx=5, pady=(0, 4))
        name_row = ttk.Frame(right)
        name_row.pack(anchor="w", padx=5, pady=(0, 8))
        ttk.Label(name_row, text="New column name for the 'One row per...' layout:").pack(side="left")
        self.new_col_name = tk.StringVar()
        ttk.Entry(name_row, textvariable=self.new_col_name, width=14).pack(side="left", padx=6)

        ttk.Label(right, text="Extracted table preview").pack(anchor="w", padx=5)
        edit_bar = ttk.Frame(right)
        edit_bar.pack(fill="x", padx=5, pady=(2, 0))
        ttk.Button(edit_bar, text="Rename column", command=self.rename_column).pack(side="left", padx=2)
        ttk.Button(edit_bar, text="Delete column", command=self.delete_column).pack(side="left", padx=2)
        ttk.Button(edit_bar, text="Reset columns", command=self.reset_edits).pack(side="left", padx=2)
        ttk.Button(edit_bar, text="Load into Target", command=self.load_clicked).pack(side="right", padx=2)
        self.remember_edits = tk.BooleanVar(value=True)
        ttk.Checkbutton(right, text="Remember column edits for the next tables",
                        variable=self.remember_edits).pack(anchor="w", padx=5)
        self.pause_load = tk.BooleanVar(value=True)
        ttk.Checkbutton(right, text="Wait for my column edits before loading into the Target file",
                        variable=self.pause_load).pack(anchor="w", padx=5)
        ttk.Label(right, foreground="#555",
                  text="Click a column header, then Rename / Delete. Or right-click a header; "
                       "double-click renames.").pack(anchor="w", padx=5)
        preview_frame = ttk.Frame(right)
        preview_frame.pack(fill="both", expand=True, padx=5, pady=5)

        self.tree = ttk.Treeview(preview_frame, show="headings")
        tree_y = ttk.Scrollbar(preview_frame, orient="vertical", command=self.tree.yview)
        tree_x = ttk.Scrollbar(preview_frame, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=tree_y.set, xscrollcommand=tree_x.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        tree_y.grid(row=0, column=1, sticky="ns")
        tree_x.grid(row=1, column=0, sticky="ew")
        preview_frame.rowconfigure(0, weight=1)
        preview_frame.columnconfigure(0, weight=1)
        if sys.platform == "darwin":
            self.tree.bind("<Button-2>", self.header_menu)
            self.tree.bind("<Control-Button-1>", self.header_menu)
        else:
            self.tree.bind("<Button-3>", self.header_menu)
        self.tree.bind("<Double-1>", self.header_double)

        ttk.Label(
            right,
            text=("Instructions:\n"
                  "1. Open a PDF. The performance table is found for you.\n"
                  "    If none is found, draw a box around the table yourself.\n"
                  "2. Zoom with Zoom +/-, Ctrl + mouse wheel, or Ctrl +/-.\n"
                  "    Move the PDF: switch on Hand, or drag with the\n"
                  "    middle mouse button.\n"
                  "3. Drag a box around each table (one box per table,\n"
                  "    on any page). Drag its white handles to resize,\n"
                  "    drag inside it to move, right-click to remove.\n"
                  "4. Click Extract Tables: all tables are combined.\n"
                  "5. With a Target file set, columns are matched to its\n"
                  "    header and the rows are added. A .xlsx target gets\n"
                  "    one tab per PDF (tab name = PDF file name);\n"
                  "    a .csv target keeps everything in one sheet.\n"
                  "    Without a target, use Save CSV."),
            justify="left", wraplength=380
        ).pack(anchor="w", padx=8, pady=8)

        self.root.protocol("WM_DELETE_WINDOW", self.close)

    # --------------------------------------------------
    # Open PDF
    # --------------------------------------------------
    def open_pdf(self):
        path = filedialog.askopenfilename(title="Select PDF",
                                          filetypes=[("PDF files", "*.pdf")])
        if path and self.load_pdf(path):
            self.folder_files = []
            self.pdf_counter.set("Single file (no folder)")

    def load_pdf(self, path):
        """Close the current PDF (if any) and show this one. Returns True on success."""
        try:
            new_pdf = pdfplumber.open(path)
            if self.pdf:
                self.pdf.close()
            self.pdf = new_pdf
            self.pdf_path = path
            self.sizes = [(float(p.width), float(p.height)) for p in self.pdf.pages]
            self.df = None
            self.raw_df = None
            self.sel_col = None
            self.selections = []
            self.clear_preview()
            self.page_var.set("1")
            self.page_count.set(f"/ {len(self.sizes)}")

            self.root.update_idletasks()
            self.fit_width()
            self.canvas.yview_moveto(0)
            self.status.set(f"Opened {os.path.basename(path)} ({len(self.sizes)} pages)")
            note = self.ensure_sheet()
            if note:
                self.status.set(self.status.get() + "   " + note)
            if self.select_mode.get() == "auto":
                self.root.update_idletasks()
                if self.auto_find_tables(quiet=True) and self.auto_extract.get():
                    self.extract_table()
            return True
        except Exception as exc:
            messagebox.showerror("PDF Error", f"{os.path.basename(path)}\n{exc}")
            return False

    # --------------------------------------------------
    # Folder of PDFs: open one, then replace it with the next
    # --------------------------------------------------
    def browse_folder(self):
        folder = filedialog.askdirectory(title="Select folder with PDFs")
        if folder:
            self.folder_var.set(folder)
            self.load_folder()

    def load_folder(self):
        folder = self.folder_var.get().strip().strip('"')
        if not os.path.isdir(folder):
            messagebox.showerror("Folder not found", f"Cannot find this folder:\n{folder}")
            return
        files = [os.path.join(folder, f) for f in os.listdir(folder)
                 if f.lower().endswith(".pdf")]
        natural = lambda p: [int(t) if t.isdigit() else t.lower()
                             for t in re.split(r"(\d+)", os.path.basename(p))]
        files.sort(key=natural)             # file2.pdf comes before file10.pdf
        if not files:
            messagebox.showwarning("No PDFs", "This folder has no .pdf files.")
            return
        self.folder_files = files
        self.folder_index = 0
        self.show_folder_pdf()

    def show_folder_pdf(self):
        path = self.folder_files[self.folder_index]
        name = os.path.basename(path)
        short = name if len(name) <= 22 else name[:19] + "..."
        self.pdf_counter.set(f"PDF {self.folder_index + 1} of "
                             f"{len(self.folder_files)}: {short}")
        self.load_pdf(path)

    def step_pdf(self, step):
        if not self.folder_files:
            messagebox.showwarning("No folder", "Enter a folder path and click Load Folder first.")
            return
        new = self.folder_index + step
        if not 0 <= new < len(self.folder_files):
            self.status.set("This is the last PDF in the folder." if step > 0
                            else "This is the first PDF in the folder.")
            return
        self.folder_index = new
        self.show_folder_pdf()

    # --------------------------------------------------
    # Target CSV: predefined columns, matching, loading
    # --------------------------------------------------
    def target_path(self):
        return self.target_var.get().strip().strip('"')

    def choose_target(self):
        path = filedialog.asksaveasfilename(
            title="Choose an existing file, or type a name for a new one "
                  "(.xlsx = one tab per PDF, .csv = one sheet)",
            defaultextension=".xlsx", confirmoverwrite=False,
            filetypes=[("Excel workbook (one tab per PDF)", "*.xlsx"),
                       ("CSV files", "*.csv")])
        if path:
            self.target_var.set(path)
            self.apply_target()

    def target_columns(self, path):
        """Predefined columns of the target (CSV header, or Excel columns)."""
        if is_excel(path):
            try:
                return self.xlsx_cols.get(path) or read_xlsx_header(path)
            except Exception:
                return []
        return read_csv_header(path)[0]

    def target_meta(self, path):
        """(groups, names) when the Excel target uses a two-row header, else None."""
        meta = self.xlsx_meta.get(path)
        if meta:
            return meta
        try:
            _, groups, names = read_xlsx_layout(path)
        except Exception:
            return None
        return (groups, names) if groups else None

    def ensure_sheet(self):
        """Excel target: give the open PDF its own tab, named after the file.
        Returns a short message for the status bar ('' if not applicable)."""
        path = self.target_path()
        if not (self.auto_sheet.get() and self.pdf_path and is_excel(path)):
            return ""
        name = os.path.basename(path)
        try:
            sheet = sheet_name_for(self.pdf_path)
            if os.path.isfile(path) and sheet_exists(path, sheet):
                return f"Tab '{sheet}' already exists in {name}."
            append_xlsx(path, sheet, [], self.target_columns(path), self.target_meta(path))
            self.refresh_target()
            return f"New tab '{sheet}' created in {name}."
        except ImportError:
            return "Excel files need openpyxl:  pip install openpyxl"
        except Exception as exc:
            return f"Could not create the tab ({exc}). Close the workbook if it is open in Excel."

    def apply_target(self):
        self.refresh_target()
        note = self.ensure_sheet()
        if note:
            self.status.set(note)

    def refresh_target(self):
        path = self.target_path()
        if not path:
            self.target_info.set("No target file. Extracted tables will be saved with Save CSV.")
            return
        cols = self.target_columns(path)
        if cols:
            text = ", ".join(cols)
            self.target_info.set(f"{len(cols)} columns: "
                                 f"{text if len(text) <= 110 else text[:107] + '...'}")
        else:
            self.target_info.set("This CSV has no columns yet. Click Set Columns... "
                                 "(or extract and use the table's own columns).")

    def set_columns(self):
        if not self.target_path():
            self.choose_target()
        path = self.target_path()
        if not path:
            return
        current = self.target_columns(path)

        win = tk.Toplevel(self.root)
        win.title("Set CSV columns")
        win.transient(self.root)
        win.grab_set()
        ttk.Label(win, padding=10, justify="left",
                  text="Column names for the CSV, one per line\n"
                       "(or separated by commas), in the order you want:").pack(anchor="w")
        box = tk.Text(win, width=44, height=12)
        box.pack(padx=10)
        box.insert("1.0", "\n".join(current))

        def save():
            cols = [c.strip() for c in re.split(r"[,\n]+", box.get("1.0", "end")) if c.strip()]
            if not cols:
                messagebox.showwarning("No columns", "Enter at least one column name.", parent=win)
                return
            if len(set(cols)) != len(cols):
                messagebox.showwarning("Duplicate names",
                                       "Each column name must be unique.", parent=win)
                return
            if is_excel(path):             # Excel: columns apply to every new tab
                self.xlsx_cols[path] = cols
                self.xlsx_meta.pop(path, None)
                self.refresh_target()
                win.destroy()
                return
            try:
                if current and os.path.getsize(path) > 0:
                    with open(path, newline="", encoding=read_csv_header(path)[1]) as f:
                        has_rows = sum(1 for _ in csv.reader(f)) > 1
                    if has_rows and not messagebox.askyesno(
                            "Replace header?",
                            "This CSV already contains data rows. Only the header line "
                            "will be replaced; existing rows are not changed.\n\nContinue?",
                            parent=win):
                        return
                write_header(path, cols)
            except Exception as exc:
                messagebox.showerror("Save Error", str(exc), parent=win)
                return
            self.refresh_target()
            win.destroy()

        row = ttk.Frame(win, padding=10)
        row.pack(fill="x")
        ttk.Button(row, text="Save columns", command=save).pack(side="right", padx=4)
        ttk.Button(row, text="Cancel", command=win.destroy).pack(side="right")
        self.root.wait_window(win)

    def match_dialog(self, template, extracted, preset):
        """Let the user match each CSV column to an extracted column.
        Returns (list of extracted names or None per CSV column, remember) or (None, False)."""
        win = tk.Toplevel(self.root)
        win.title("Match columns")
        win.transient(self.root)
        win.grab_set()
        blank = "(leave empty)"
        ttk.Label(win, padding=10,
                  text="Match every CSV column with a column from the extracted table:"
                  ).grid(row=0, column=0, columnspan=3, sticky="w")
        choices, result = [], {}
        for i, name in enumerate(template):
            ttk.Label(win, text=name).grid(row=i + 1, column=0, sticky="w", padx=10, pady=3)
            ttk.Label(win, text="<-").grid(row=i + 1, column=1)
            var = tk.StringVar(value=preset[i] if preset[i] is not None else blank)
            ttk.Combobox(win, textvariable=var, values=[blank] + list(extracted),
                         state="readonly", width=36).grid(row=i + 1, column=2, padx=10, pady=3)
            choices.append(var)
        remember = tk.BooleanVar(value=True)
        n = len(template) + 1
        ttk.Checkbutton(win, text="Remember this matching for tables with the same columns",
                        variable=remember).grid(row=n, column=0, columnspan=3,
                                                sticky="w", padx=10, pady=6)

        def ok():
            result["map"] = [None if v.get() == blank else v.get() for v in choices]
            result["remember"] = remember.get()
            win.destroy()

        row = ttk.Frame(win, padding=10)
        row.grid(row=n + 1, column=0, columnspan=3, sticky="e")
        ttk.Button(row, text="Load into CSV", command=ok).pack(side="right", padx=4)
        ttk.Button(row, text="Cancel", command=win.destroy).pack(side="right")
        self.root.wait_window(win)
        return result.get("map"), result.get("remember", False)

    def load_into_target(self):
        """Match the extracted columns to the target CSV's header and add the rows."""
        path = self.target_path()
        df = self.df
        if not path or df is None:
            return False

        key = (self.pdf_path, tuple((s["page"], tuple(round(v, 1) for v in s["bbox"]))
                                    for s in self.selections))
        if key == self.loaded_key and not messagebox.askyesno(
                "Already loaded",
                "These tables were already added to the CSV.\n\nAdd them again?"):
            return False

        extracted = list(df.columns)
        template = self.target_columns(path)
        excel = is_excel(path)
        new_file = not template
        own = self.own_header and excel

        if own:                          # another table type: its own header on its own tab
            template, mapping, new_file = list(extracted), list(extracted), False
        elif new_file:
            if not messagebox.askyesno(
                    "No columns yet",
                    "The target CSV has no columns yet.\n\n"
                    "Use the extracted table's columns as its header?"):
                return False
            template, mapping = list(extracted), list(extracted)
            if excel:
                self.xlsx_cols[path] = template
                if self.df_meta:
                    self.xlsx_meta[path] = self.df_meta
                else:
                    self.xlsx_meta.pop(path, None)
        else:
            sig = (tuple(_norm(c) for c in template), tuple(_norm(c) for c in extracted))
            mapping = self.mapping_memory.get(sig)
            if mapping is None or self.confirm_always.get():
                preset = mapping or [None if j is None else extracted[j]
                                     for j in auto_match(template, extracted)]
                mapping, remember = self.match_dialog(template, extracted, preset)
                if mapping is None:
                    self.status.set("Loading into the CSV was cancelled.")
                    return False
                if remember:
                    self.mapping_memory[sig] = mapping
            if not any(mapping):
                messagebox.showwarning("Nothing matched",
                                       "No column was matched, so nothing was added.")
                return False

        rows = [["" if m is None or pd.isna(row[m]) else str(row[m]) for m in mapping]
                for _, row in df.iterrows()]
        try:
            if excel:
                tab = append_xlsx(path, sheet_name_for(self.pdf_path, self.sheet_suffix), rows, template,
                                  self.df_meta if own else self.target_meta(path))
                dest = f"tab '{tab}' of {os.path.basename(path)}"
            else:
                append_rows(path, rows, header=template if new_file else None)
                dest = os.path.basename(path)
        except ImportError:
            messagebox.showerror("Excel support missing",
                                 "Excel files need the openpyxl package.\n\n"
                                 "Install it with:  pip install openpyxl")
            return False
        except Exception as exc:
            messagebox.showerror("File Error", f"Could not write to the file:\n{exc}\n\n"
                                 "If it is open in Excel, close it and try again.")
            return False

        self.loaded_key = key
        self.raw_df = None
        self.sel_col = None
        if list(template) != extracted:
            self.df_meta = None
        self.df = pd.DataFrame(rows, columns=unique_names(template))
        self.show_preview()
        self.refresh_target()
        unused = [c for c in extracted if c not in mapping]
        self.status.set(
            f"Loaded {len(rows)} rows into {dest} "
            f"({sum(1 for m in mapping if m)} of {len(template)} columns matched)."
            + (f" Not used: {', '.join(unused)}" if unused else ""))
        return True

    # --------------------------------------------------
    # Automatic search for the performance table
    # --------------------------------------------------
    def find_tables_in(self, pdf):
        """[{'page': index, 'bbox': (...), 'rows': n}] for every performance table."""
        words = [k.strip() for k in re.split(r"[,;\n]+", self.kw_var.get()) if k.strip()]
        try:
            need = max(1, int(self.min_hits.get()))
        except (ValueError, tk.TclError):
            need = 3
        found = []
        for i, page in enumerate(pdf.pages):
            try:
                hits = find_performance_tables(page, words, need)
            except Exception:
                hits = []
            found += [{"page": i, "bbox": h["bbox"], "rows": h["rows"], "hits": h["hits"]} for h in hits]
        return found

    def group_found(self, found):
        """Tables with the same header belong together (a table that continues on the next
        page). Returns the groups, best match first."""
        groups = {}
        for f in found:
            try:
                rows = self.extract_one({"page": f["page"], "bbox": f["bbox"]})
            except Exception:
                rows = None
            sig = tuple(_norm(c) for c in rows[0]) if rows else ("?", f["page"])
            groups.setdefault(sig, []).append(f)
        out = list(groups.values())
        out.sort(key=lambda g: (-max(len(x["hits"]) for x in g), -sum(x["rows"] for x in g)))
        return out

    def auto_find_tables(self, quiet=False):
        """Search every page, draw a box around each performance table found."""
        if not self.pdf:
            if not quiet:
                messagebox.showwarning("No PDF", "Please open a PDF first.")
            return False
        self.status.set("Searching the PDF for performance tables...")
        self.root.update_idletasks()
        found = self.find_tables_in(self.pdf)
        if not found:
            self.status.set("No performance table found in this PDF. Draw a box around the table "
                            "yourself, then click Extract Tables.")
            if not quiet:
                messagebox.showinfo(
                    "Auto-Find Tables",
                    "No performance table was found.\n\nDraw a box around the table yourself and "
                    "click Extract Tables. Or lower 'Header words needed to match', or add words "
                    "that appear in the table header.")
            return False
        extra = ""
        groups = self.group_found(found)
        if len(groups) > 1 and self.multi_mode.get().startswith("Best"):
            extra = (f" Another table type was found on page "
                     f"{groups[1][0]['page'] + 1}; set 'Several table types' to All to use it.")
            found = groups[0]
        self.selections = [{"page": f["page"], "bbox": f["bbox"]} for f in found]
        self.draw_selection()
        first = found[0]
        y = self.boxes[first["page"]][1] + first["bbox"][1] * self.scale() - 60
        self.canvas.yview_moveto(max(0, y / self.total_h))
        pages = ", ".join(str(p) for p in sorted({f["page"] + 1 for f in found}))
        self.status.set(f"Found {len(found)} performance table(s) on page {pages}. "
                        "Drag the handles to adjust a box if needed." + extra)
        self.schedule_render()
        return True

    def run_folder_auto(self):
        """Every PDF of the folder: find the performance table, extract, load into the target.
        PDFs without a table are listed so you can open them and select the table yourself."""
        if not self.folder_files:
            messagebox.showwarning("No folder", "Enter a folder path and click Load Folder first.")
            return
        if not self.target_path():
            messagebox.showwarning(
                "No target file",
                "Choose a Target file first (CSV or Excel). The data of every PDF is added there.")
            return
        n = len(self.folder_files)
        if not messagebox.askyesno(
                "Run folder automatically",
                f"Find the performance table in each of the {n} PDFs and load it into:\n"
                f"{self.target_path()}\n\nPDFs without a table are listed afterwards, "
                f"so you can select the table yourself.\n\nContinue?"):
            return
        if self.pdf:
            self.pdf.close()
            self.pdf = None
        report = []                                  # (label, result, path)
        for idx, path in enumerate(self.folder_files, 1):
            name = os.path.basename(path)
            add = lambda label, msg, p=path: report.append((label, msg, p))
            self.pdf_counter.set(f"Auto {idx} of {n}: {name if len(name) <= 22 else name[:19] + '...'}")
            self.status.set(f"Processing {name} ...")
            self.root.update()
            try:
                pdf = pdfplumber.open(path)
            except Exception as exc:
                report.append((name, f"could not open ({exc})", None))
                continue
            self.pdf, self.pdf_path, self.selections, self.batch_log = pdf, path, [], []
            try:
                found = self.find_tables_in(pdf)
                if not found:
                    add(name, "no performance table found")
                    continue
                groups = self.group_found(found)
                if self.multi_mode.get().startswith("Best") or not is_excel(self.target_path()):
                    if len(groups) > 1 and not self.multi_mode.get().startswith("Best"):
                        add(name, "another table type skipped (a CSV target has one set of columns)")
                    groups = groups[:1]
                for gi, group in enumerate(groups):
                    self.sheet_suffix = "" if gi == 0 else f" ({gi + 1})"
                    self.own_header = gi > 0
                    self.selections = [{"page": f["page"], "bbox": f["bbox"]} for f in group]
                    self.batch_log = []
                    label = name + (f"  [{self.sheet_suffix.strip()}]" if gi else "")
                    ok = self.extract_table(quiet=True, force_load=True)
                    if ok and self.last_load_ok:
                        add(label, f"OK  ({len(group)} table(s), {len(self.df)} rows)")
                    elif ok:
                        add(label, "extracted but not loaded into the file")
                    else:
                        add(label, "extraction failed: " + "; ".join(self.batch_log))
            except Exception as exc:
                add(name, f"error: {exc}")
            finally:
                pdf.close()
                self.pdf = None
                self.sheet_suffix = ""
                self.own_header = False
        self.folder_index = 0
        self.show_folder_pdf()
        done = sum(1 for r in report if r[1].startswith("OK"))
        todo = len(self.manual_items(report))
        self.status.set(f"Folder finished: {done} table(s) loaded into "
                        f"{os.path.basename(self.target_path())}."
                        + (f" {todo} PDF(s) need you to select the table." if todo else ""))
        self.show_report(f"{done} table(s) loaded from {n} PDFs", report)

    @staticmethod
    def manual_items(report):
        """PDFs of a folder run where the user has to select the table: [(name, path)]."""
        seen, out = set(), []
        for label, result, path in report:
            if path and path not in seen and not result.startswith(("OK", "could not open", "another table")):
                seen.add(path)
                out.append((os.path.basename(path), path))
        return out

    def open_manual(self, path):
        """Open one PDF of the folder so the table can be selected by hand."""
        if path in self.folder_files:
            self.folder_index = self.folder_files.index(path)
            self.show_folder_pdf()
        else:
            self.load_pdf(path)

    def show_report(self, title, report):
        win = tk.Toplevel(self.root)
        win.title("Folder report")
        ttk.Label(win, text=title, padding=10, font=("Arial", 11, "bold")).pack(anchor="w")
        box = tk.Text(win, width=90, height=16, wrap="none")
        box.pack(fill="both", expand=True, padx=10)
        for label, result, _p in report:
            box.insert("end", f"{'[ok]  ' if result.startswith('OK') else '[!!]  '}{label}  -  {result}\n")
        box.configure(state="disabled")
        manual = self.manual_items(report)
        if manual:
            ttk.Label(win, padding=(10, 8, 10, 2),
                      text="These PDFs need you to select the table yourself.\n"
                           "Double-click one (or select it and click the button), draw a box "
                           "around the table, then Extract Tables and Load into Target:"
                      ).pack(anchor="w")
            lb = tk.Listbox(win, height=min(8, len(manual)))
            for name, _p in manual:
                lb.insert("end", name)
            lb.selection_set(0)
            lb.pack(fill="x", padx=10)

            def open_selected(event=None):
                sel = lb.curselection()
                if sel:
                    self.open_manual(manual[sel[0]][1])

            lb.bind("<Double-Button-1>", open_selected)
            ttk.Button(win, text="Open selected PDF", command=open_selected).pack(pady=(6, 0))
        ttk.Button(win, text="Close", command=win.destroy).pack(pady=8)

    # --------------------------------------------------
    # Layout, zoom and lazy page rendering
    # --------------------------------------------------
    def scale(self):
        return self.zoom * BASE

    def layout(self):
        s = self.scale()
        max_w = max(w for w, _ in self.sizes) * s
        y = GAP
        self.boxes = []
        for w, h in self.sizes:
            pw, ph = w * s, h * s
            x = GAP + (max_w - pw) / 2
            self.boxes.append((x, y, pw, ph))
            y += ph + GAP
        self.total_w = max_w + 2 * GAP
        self.total_h = y
        self.canvas.configure(scrollregion=(0, 0, self.total_w, self.total_h))

    def redraw(self):
        """Rebuild page placeholders (after open or zoom), keep the view centred."""
        if not self.sizes:
            return
        old_h = getattr(self, "total_h", 0)
        old_w = getattr(self, "total_w", 0)
        ya, yb = self.canvas.yview()
        xa, xb = self.canvas.xview()
        cy, cx = (ya + yb) / 2 * old_h, (xa + xb) / 2 * old_w

        self.canvas.delete("all")
        self.images.clear()
        self.layout()

        for i, (x, y, w, h) in enumerate(self.boxes):
            self.canvas.create_rectangle(x, y, x + w, y + h, fill="white", outline="#555")
            self.canvas.create_text(x + w / 2, y + h / 2, text=f"Page {i + 1}", fill="#aaa")

        if old_h:
            ch, cw = self.canvas.winfo_height(), self.canvas.winfo_width()
            self.canvas.yview_moveto(max(0, (cy - ch / 2) / self.total_h))
            self.canvas.xview_moveto(max(0, (cx - cw / 2) / self.total_w))

        self.draw_selection()
        self.render_visible()

    def schedule_render(self):
        if self.render_job:
            self.root.after_cancel(self.render_job)
        self.render_job = self.root.after(40, self.render_visible)

    def _yscroll(self, a, b):
        self.scroll_y.set(a, b)
        self.schedule_render()

    def render_visible(self):
        self.render_job = None
        if not self.pdf or not self.boxes:
            return

        top = self.canvas.canvasy(0)
        height = self.canvas.winfo_height()
        bottom = top + height
        margin = height // 2

        visible = [i for i, (_, y, _, h) in enumerate(self.boxes)
                   if y + h >= top - margin and y <= bottom + margin]
        if not visible:
            return

        for i in visible:
            if i in self.images:
                continue
            x, y, w, h = self.boxes[i]
            img = self.pdf.pages[i].to_image(resolution=72 * self.scale()).original
            size = (max(1, round(w)), max(1, round(h)))
            if img.size != size:
                img = img.resize(size)
            photo = ImageTk.PhotoImage(img)
            item = self.canvas.create_image(x, y, anchor="nw", image=photo)
            self.images[i] = (photo, item)

        # Free memory for pages that are far away
        for i in [k for k in self.images if k < visible[0] - 3 or k > visible[-1] + 3]:
            self.canvas.delete(self.images[i][1])
            del self.images[i]

        self.canvas.tag_raise("sel")

        # Show the page in the middle of the view
        mid = top + height / 2
        for i, (_, y, _, h) in enumerate(self.boxes):
            if y <= mid <= y + h + GAP:
                self.page_var.set(str(i + 1))
                break

    def set_zoom(self, value):
        if not self.sizes:
            return
        value = max(MIN_ZOOM, min(MAX_ZOOM, value))
        self.zoom = value
        self.zoom_label.set(f"{round(value * 100)}%")
        self.redraw()

    def zoom_by(self, factor):
        self.set_zoom(self.zoom * factor)

    def fit_width(self):
        if not self.sizes:
            return
        max_w = max(w for w, _ in self.sizes)
        avail = self.canvas.winfo_width() - 2 * GAP - 20
        self.set_zoom(avail / (max_w * BASE))

    def go_to_page(self):
        if not self.pdf:
            messagebox.showwarning("No PDF", "Please open a PDF first.")
            return
        try:
            n = int(self.page_var.get())
            if not 1 <= n <= len(self.boxes):
                raise ValueError("Page number is out of range.")
        except ValueError as exc:
            messagebox.showerror("Page Error", str(exc))
            return
        y = self.boxes[n - 1][1] - GAP
        self.canvas.yview_moveto(max(0, y / self.total_h))

    def on_wheel(self, event):
        if event.num == 4:
            direction = 1
        elif event.num == 5:
            direction = -1
        else:
            direction = 1 if event.delta > 0 else -1

        if event.state & 0x4:            # Ctrl: zoom
            self.zoom_by(1.15 if direction > 0 else 1 / 1.15)
        elif event.state & 0x1:          # Shift: horizontal scroll
            self.canvas.xview_scroll(-direction * 3, "units")
        else:
            self.canvas.yview_scroll(-direction * 3, "units")

    # --------------------------------------------------
    # Drag to select table areas (stored in PDF points,
    # so selections survive zooming). Any number of boxes.
    # --------------------------------------------------
    def page_at(self, x, y):
        for i, (bx, by, bw, bh) in enumerate(self.boxes):
            if bx <= x <= bx + bw and by <= y <= by + bh:
                return i
        return None

    # --- moving the PDF with the mouse (Hand tool / middle button) ---
    def update_cursor(self):
        self.canvas.configure(cursor="fleur" if self.hand_mode.get() else "crosshair")

    def pan_start(self, event):
        self.canvas.scan_mark(event.x, event.y)
        self.panning = True
        self.canvas.configure(cursor="fleur")

    def pan_move(self, event):
        if self.panning:
            self.canvas.scan_dragto(event.x, event.y, gain=1)

    def pan_end(self, event):
        self.panning = False
        self.update_cursor()

    def start_crop(self, event):
        if self.hand_mode.get():          # Hand tool on: left drag moves the PDF
            self.pan_start(event)
            return
        if not self.boxes:
            return
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        hit = self.hit_test(x, y)
        if hit:                           # grab an existing box: resize or move it
            idx, mode = hit
            self.edit = {"idx": idx, "mode": mode, "sx": x, "sy": y,
                         "bbox": self.selections[idx]["bbox"]}
            return
        page = self.page_at(x, y)
        if page is None:
            return
        self.drag_page = page
        self.start_x, self.start_y = x, y
        self.rect_id = self.canvas.create_rectangle(x, y, x, y, outline="red",
                                                    width=2, tags="sel")

    def _clamp(self, x, y):
        bx, by, bw, bh = self.boxes[self.drag_page]
        return min(max(x, bx), bx + bw), min(max(y, by), by + bh)

    def move_crop(self, event):
        if self.panning:
            self.pan_move(event)
            return
        if self.edit:
            self.apply_edit(self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
            return
        if self.drag_page is None or self.rect_id is None:
            return
        x, y = self._clamp(self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
        self.canvas.coords(self.rect_id, self.start_x, self.start_y, x, y)

    def finish_crop(self, event):
        if self.panning:
            self.pan_end(event)
            return
        if self.edit:
            self.edit = None
            self.status.set(f"{len(self.selections)} table(s) selected. "
                            "Drag a handle to resize a box, or drag inside it to move it.")
            return
        if self.drag_page is None:
            return
        page = self.drag_page
        x, y = self._clamp(self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
        self.drag_page = None
        x0, x1 = sorted([self.start_x, x])
        y0, y1 = sorted([self.start_y, y])

        if x1 - x0 < 10 or y1 - y0 < 10:
            self.draw_selection()            # drops the tiny temporary box
            self.status.set("Selection too small. Try again.")
            return

        bx, by, _, _ = self.boxes[page]
        s = self.scale()
        pw, ph = self.sizes[page]
        self.selections.append({"page": page, "bbox": (
            max(0, (x0 - bx) / s), max(0, (y0 - by) / s),
            min(pw, (x1 - bx) / s), min(ph, (y1 - by) / s))})
        self.draw_selection()
        self.status.set(f"{len(self.selections)} table(s) selected. "
                        "Draw more boxes, or click Extract + Save CSV.")

    HANDLE = 4      # half-size of a resize handle (pixels)
    GRAB = 7        # how close the mouse must be to grab a handle (pixels)

    def _canvas_rect(self, sel):
        bx, by, _, _ = self.boxes[sel["page"]]
        s = self.scale()
        l, t, r, b = sel["bbox"]
        return bx + l * s, by + t * s, bx + r * s, by + b * s

    @staticmethod
    def _handle_points(rect):
        l, t, r, b = rect
        mx, my = (l + r) / 2, (t + b) / 2
        return {"nw": (l, t), "n": (mx, t), "ne": (r, t), "e": (r, my),
                "se": (r, b), "s": (mx, b), "sw": (l, b), "w": (l, my)}

    def draw_selection(self):
        self.canvas.delete("sel")
        h = self.HANDLE
        for n, sel in enumerate(self.selections, 1):
            rect = self._canvas_rect(sel)
            self.canvas.create_rectangle(*rect, outline="red", width=2, tags="sel")
            self.canvas.create_text(rect[0] + 4, rect[1] + 2, text=f"Table {n}",
                                    anchor="nw", fill="red",
                                    font=("Arial", 11, "bold"), tags="sel")
            for hx, hy in self._handle_points(rect).values():
                self.canvas.create_rectangle(hx - h, hy - h, hx + h, hy + h,
                                             fill="white", outline="red", tags="sel")

    def hit_test(self, x, y):
        """Which box handle (or box body) is under the mouse? -> (index, mode) or None."""
        g = self.GRAB
        for i in range(len(self.selections) - 1, -1, -1):
            rect = self._canvas_rect(self.selections[i])
            for name, (hx, hy) in self._handle_points(rect).items():
                if abs(x - hx) <= g and abs(y - hy) <= g:
                    return i, name
        for i in range(len(self.selections) - 1, -1, -1):
            l, t, r, b = self._canvas_rect(self.selections[i])
            if l <= x <= r and t <= y <= b:
                return i, "move"
        return None

    def apply_edit(self, x, y):
        e = self.edit
        sel = self.selections[e["idx"]]
        s = self.scale()
        dx, dy = (x - e["sx"]) / s, (y - e["sy"]) / s
        l, t, r, b = e["bbox"]
        pw, ph = self.sizes[sel["page"]]
        mode, MIN = e["mode"], 6
        if mode == "move":
            w, h = r - l, b - t
            l = min(max(0, l + dx), pw - w)
            t = min(max(0, t + dy), ph - h)
            r, b = l + w, t + h
        else:
            if "w" in mode:
                l = min(max(0, l + dx), r - MIN)
            if "e" in mode:
                r = max(min(pw, r + dx), l + MIN)
            if "n" in mode:
                t = min(max(0, t + dy), b - MIN)
            if "s" in mode:
                b = max(min(ph, b + dy), t + MIN)
        sel["bbox"] = (l, t, r, b)
        self.draw_selection()

    def on_motion(self, event):
        """Show a resize / move cursor when the mouse is over a box."""
        if self.panning or self.edit or self.drag_page is not None or self.hand_mode.get():
            return
        hit = self.hit_test(self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
        cursors = {"n": "sb_v_double_arrow", "s": "sb_v_double_arrow",
                   "e": "sb_h_double_arrow", "w": "sb_h_double_arrow",
                   "move": "fleur"}
        cursor = "crosshair" if not hit else cursors.get(hit[1], "sizing")
        try:
            self.canvas.configure(cursor=cursor)
        except tk.TclError:
            self.canvas.configure(cursor="crosshair")

    def remove_at(self, event):
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        s = self.scale()
        for i in range(len(self.selections) - 1, -1, -1):
            sel = self.selections[i]
            bx, by, _, _ = self.boxes[sel["page"]]
            l, t, r, b = sel["bbox"]
            if bx + l * s <= x <= bx + r * s and by + t * s <= y <= by + b * s:
                del self.selections[i]
                self.draw_selection()
                self.status.set(f"Removed a box. {len(self.selections)} table(s) selected.")
                return

    def undo_selection(self):
        if self.selections:
            self.selections.pop()
            self.draw_selection()
        self.status.set(f"{len(self.selections)} table(s) selected.")

    def clear_selection(self):
        self.selections = []
        self.drag_page = None
        self.draw_selection()
        self.status.set("All selections cleared.")

    # --------------------------------------------------
    # Extract tables using pdfplumber
    # --------------------------------------------------
    def extract_one(self, sel):
        """Return one table as a list of rows (first row = header), or None."""
        full_page = self.pdf.pages[sel["page"]]
        cropped = full_page.crop(sel["bbox"])
        if self.skip_hidden.get():
            cropped = drop_hidden_text(full_page, cropped)
        mode = self.method.get()
        table = None

        text_settings = {
            "vertical_strategy": "text",
            "horizontal_strategy": "text",
            "min_words_vertical": 1,
            "min_words_horizontal": 1,
            "text_x_tolerance": 3,
            "text_y_tolerance": 3,
        }
        line_settings = {
            "vertical_strategy": "lines",
            "horizontal_strategy": "lines",
            "snap_tolerance": 5,
            "join_tolerance": 5,
        }

        if mode.startswith("Smart"):
            table = smart_table(cropped, float(self.col_gap.get()),
                                self.fill_merged.get())
            if not table:            # nothing found: try the other methods
                mode = "Automatic"

        if mode == "Automatic":
            table = cropped.extract_table()
            if not table:
                table = cropped.extract_table(table_settings=text_settings)
            if not table:
                table = cropped.extract_table(table_settings=line_settings)
        elif mode == "Lines":
            table = cropped.extract_table(table_settings=line_settings)
        elif mode == "Text":
            table = cropped.extract_table(table_settings=text_settings)

        if not table:
            return None

        rows = []
        for row in table:
            # None = cell covered by a merged cell; "" = truly empty cell
            row = [None if cell is None
                   else re.sub(r"\s*\n\s*", " ", str(cell)).strip()
                   for cell in row]
            if any(row):
                rows.append(row)
        if not rows:
            return None

        width = max(len(row) for row in rows)
        rows = [row + [None] * (width - len(row)) for row in rows]
        if self.fill_merged.get():
            rows = self.fill_merged_cells(rows)
        rows = [["" if c is None else c for c in row] for row in rows]
        groups = getattr(table, "groups", None)
        usable = bool(groups and any(groups) and len(groups) == len(rows[0]))
        layout = self.table_layout.get()
        if usable and layout.startswith("One row"):
            out = reshape_long(rows, groups, table.names, self.new_col_name.get().strip())
            if out is not rows:
                return out
        res = SmartTable(rows)
        if usable and layout.startswith("Two-row"):
            res.groups, res.names = list(groups), list(table.names)
        return res

    def combine_tables(self, results):
        """results: [(table number, page number, rows)]. Stack them under one header."""
        width = max(len(rows[0]) for _, _, rows in results)
        pad = lambda r: r + [""] * (width - len(r))
        header = pad(results[0][2][0])
        norm = lambda r: [c.strip().lower() for c in r]
        out, notes = [], []

        for idx, (n, page, rows) in enumerate(results):
            body = [pad(r) for r in rows]
            if idx == 0 or norm(body[0]) == norm(header):
                body = body[1:]          # same header as the first table: drop it
            else:
                notes.append(f"Table {n} has a different header, "
                             "so its header row was kept as a data row.")
            for r in body:
                out.append(([os.path.basename(self.pdf_path or ""), str(page), str(n)]
                            if self.add_source.get() else []) + r)

        self.header_meta = None
        metas = [(getattr(rows, "groups", None), getattr(rows, "names", None))
                 for _, _, rows in results]
        g0, n0 = metas[0]
        if g0 and not notes and len(g0) == width and all(m[0] == g0 for m in metas):
            src = self.add_source.get()
            self.header_meta = ((["", "", ""] if src else []) + list(g0),
                                (["File", "Page", "Table"] if src else []) + list(n0))
        if self.add_source.get():
            header = ["File", "Page", "Table"] + header
        return [header] + out, notes

    def extract_table(self, quiet=False, force_load=False):
        self.last_load_ok = None
        if self.pdf is None:
            messagebox.showwarning("No PDF", "Open a PDF first.")
            return False
        if not self.selections:
            messagebox.showwarning("No selection",
                                   "Drag a rectangle around each table first.")
            return False

        results, problems = [], []
        for n, sel in enumerate(self.selections, 1):
            try:
                rows = self.extract_one(sel)
            except Exception as exc:
                problems.append(f"Table {n} (page {sel['page'] + 1}): {exc}")
                continue
            if rows:
                results.append((n, sel["page"] + 1, rows))
            else:
                problems.append(f"Table {n} (page {sel['page'] + 1}): no table found")

        if not results:
            if quiet:
                self.batch_log.extend(problems)
            else:
                messagebox.showwarning(
                    "No table detected",
                    "\n".join(problems) + "\n\nTry a slightly larger area or change "
                    "the extraction method.")
            return False

        rows, notes = self.combine_tables(results)

        headers, used = [], {}
        for i, value in enumerate(rows[0]):
            name = value.strip() or f"Column_{i + 1}"
            if name in used:
                used[name] += 1
                name = f"{name}_{used[name]}"
            else:
                used[name] = 1
            headers.append(name)

        if not self.remember_edits.get():
            self.edits = {}
        self.raw_df = pd.DataFrame(rows[1:], columns=headers)
        self.raw_meta = self.header_meta
        self.sel_col = None
        self.apply_edits()
        self.status.set(f"Extracted {len(results)} of {len(self.selections)} table(s): "
                        f"{len(self.df)} rows, {len(self.df.columns)} columns.")
        if problems or notes:
            if quiet:
                self.batch_log.extend(problems + notes)
            else:
                messagebox.showwarning("Check these tables", "\n".join(problems + notes))
        if self.target_path():
            if self.pause_load.get() and not force_load:
                self.status.set(self.status.get() +
                                "  Edit the columns if needed, then click Load into Target.")
            else:
                self.last_load_ok = self.load_into_target()
        return True

    # --------------------------------------------------
    # Preview
    # --------------------------------------------------
    @staticmethod
    def fill_merged_cells(rows):
        """Repeat the value of merged (row-spanning) cells on every row they cover."""
        header = ["" if c is None else c for c in rows[0]]
        data = rows[1:]
        width = len(header)

        # Leading columns that contain blanks are treated as merged-cell columns
        k = 0
        while k < width and any(not r[k] for r in data):
            k += 1

        last = [""] * width
        for r in data:
            for c in range(width):
                if r[c] is None or (r[c] == "" and c < k):
                    r[c] = last[c]
                if r[c]:
                    last[c] = r[c]

        # Blanks above the first value (text centred inside a merged cell)
        for c in range(k):
            first = next((r[c] for r in data if r[c]), "")
            for r in data:
                if r[c]:
                    break
                r[c] = first

        return [header] + data

    # --------------------------------------------------
    # Edit the columns of the preview (rename / delete)
    # --------------------------------------------------
    def apply_edits(self):
        """Build self.df from the extracted table plus the column edits."""
        raw, meta = self.raw_df, self.raw_meta
        if raw is None:
            return
        flat, origin, groups, names = [], [], [], []
        for i, col in enumerate(raw.columns):
            edit = self.edits.get(col)
            if edit and edit[0] == "delete":
                continue
            g = meta[0][i] if meta else ""
            nm = meta[1][i] if meta else col
            if edit and edit[0] == "rename":
                nm = edit[1]
                name = f"{g} {nm}".strip() if g else nm
            else:
                name = col
            flat.append(name)
            origin.append(col)
            groups.append(g)
            names.append(nm)
        if not origin:                       # never leave an empty table
            self.edits = {}
            return self.apply_edits()
        self.df = raw[origin].copy()
        self.df.columns = unique_names(flat)
        self.col_origin = origin
        self.df_meta = (groups, names) if meta else None
        self.show_preview()

    def refresh_headings(self):
        for i, column in enumerate(self.tree["columns"]):
            self.tree.heading(column, text=("\u25b6 " if i == self.sel_col else "") + column)

    def pick_column(self, idx):
        self.sel_col = idx
        self.refresh_headings()
        if self.raw_df is not None and idx < len(self.df.columns):
            self.status.set(f"Column '{self.df.columns[idx]}' picked: use Rename column / Delete column.")

    def column_at(self, event):
        if self.raw_df is None or self.tree.identify_region(event.x, event.y) != "heading":
            return None
        idx = int(self.tree.identify_column(event.x)[1:]) - 1
        return idx if 0 <= idx < len(self.col_origin) else None

    def header_menu(self, event):
        idx = self.column_at(event)
        if idx is None:
            return
        self.pick_column(idx)
        menu = tk.Menu(self.root, tearoff=0)
        menu.add_command(label=f"Rename '{self.df.columns[idx]}'...", command=self.rename_column)
        menu.add_command(label="Delete this column", command=self.delete_column)
        menu.add_separator()
        menu.add_command(label="Reset all column edits", command=self.reset_edits)
        menu.tk_popup(event.x_root, event.y_root)

    def header_double(self, event):
        idx = self.column_at(event)
        if idx is not None:
            self.pick_column(idx)
            self.rename_column()

    def _need_column(self):
        if self.raw_df is None:
            messagebox.showinfo("Edit columns", "Extract a table first. Columns can be edited "
                                "after extracting and before the data is loaded into the file.")
            return False
        if self.sel_col is None or self.sel_col >= len(self.col_origin):
            messagebox.showinfo("Edit columns", "Click a column header in the preview first.")
            return False
        return True

    def rename_column(self):
        if not self._need_column():
            return
        i = self.sel_col
        g = self.df_meta[0][i] if self.df_meta else ""
        current = self.df_meta[1][i] if self.df_meta else self.df.columns[i]
        new = simpledialog.askstring(
            "Rename column",
            "New name for this column" + (f" (shown under '{g}')" if g else "") + ":",
            initialvalue=current, parent=self.root)
        if new is None:
            return
        new = new.strip()
        if not new:
            messagebox.showwarning("Rename column", "The name cannot be empty.")
            return
        self.edits[self.col_origin[i]] = ("rename", new)
        self.apply_edits()
        self.pick_column(i)

    def delete_column(self):
        if not self._need_column():
            return
        if len(self.col_origin) <= 1:
            messagebox.showwarning("Delete column", "At least one column must stay.")
            return
        i = self.sel_col
        self.edits[self.col_origin[i]] = ("delete",)
        self.sel_col = None
        self.apply_edits()
        self.status.set("Column deleted. Use Reset columns to bring it back.")

    def reset_edits(self):
        if self.raw_df is None:
            return
        self.edits = {}
        self.sel_col = None
        self.apply_edits()
        self.status.set("All column edits were reset.")

    def load_clicked(self):
        if self.df is None:
            messagebox.showwarning("No data", "Extract a table first.")
            return
        if not self.target_path():
            messagebox.showwarning("No target file",
                                   "Choose a target file first (Target file: Choose / Create...).")
            return
        self.load_into_target()

    def clear_preview(self):
        self.tree.delete(*self.tree.get_children())
        self.tree["columns"] = ()

    def show_preview(self):
        self.clear_preview()
        columns = list(self.df.columns)
        self.tree["columns"] = columns

        for i, column in enumerate(columns):
            self.tree.heading(column, text=("\u25b6 " if i == self.sel_col else "") + column,
                              command=lambda i=i: self.pick_column(i))
            self.tree.column(column, width=130, minwidth=80, stretch=True)

        for _, row in self.df.iterrows():
            values = ["" if pd.isna(v) else str(v) for v in row]
            self.tree.insert("", "end", values=values)

    # --------------------------------------------------
    # Save CSV
    # --------------------------------------------------
    def extract_and_save(self):
        if self.extract_table() and not self.target_path():
            self.save_csv()

    def save_csv(self):
        if self.df is None:
            messagebox.showwarning("No data", "Extract the table before saving.")
            return

        default_name = "extracted_table.csv"
        if self.pdf_path:
            base = os.path.splitext(os.path.basename(self.pdf_path))[0]
            if len(self.selections) == 1:
                default_name = f"{base}_table_page_{self.selections[0]['page'] + 1}.csv"
            else:
                default_name = f"{base}_tables.csv"

        path = filedialog.asksaveasfilename(
            title="Save extracted table", initialfile=default_name,
            initialdir=os.path.dirname(self.pdf_path) if self.pdf_path else None,
            defaultextension=".csv",
            filetypes=[("CSV files", "*.csv"), ("Excel workbook", "*.xlsx")])
        if not path:
            return

        rows = [["" if pd.isna(v) else str(v) for v in r]
                for r in self.df.itertuples(index=False)]
        meta = self.df_meta if self.df_meta and len(self.df_meta[0]) == len(self.df.columns) else None
        try:
            if path.lower().endswith(".xlsx"):
                tab = append_xlsx(path, sheet_name_for(self.pdf_path or "table.pdf"),
                                  rows, list(self.df.columns), meta)
                self.status.set(f"Saved to tab '{tab}' of {path}")
            else:
                with open(path, "w", newline="", encoding="utf-8-sig") as f:
                    w = csv.writer(f)
                    if meta:                       # two header lines, like the PDF
                        w.writerows(two_row_header(*meta))
                    else:
                        w.writerow(list(self.df.columns))
                    w.writerows(rows)
                self.status.set(f"CSV saved: {path}")
            messagebox.showinfo("File created", f"Saved successfully:\n{path}")
        except ImportError:
            messagebox.showerror("Excel support missing",
                                 "Excel files need the openpyxl package.\n\n"
                                 "Install it with:  pip install openpyxl")
        except Exception as exc:
            messagebox.showerror("Save Error", str(exc))

    # --------------------------------------------------
    # Close application
    # --------------------------------------------------
    def close(self):
        if self.pdf:
            self.pdf.close()
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    app = PDFTableCropper(root)
    root.mainloop()