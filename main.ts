// news-image-20261126 v2 — "Thursday 26 November 2026: Tariffs on 14 Economies,
// Fire over Ras Tanura". Draws the whole front page in pure TypeScript (Node 22,
// stdlib only): a tiny TrueType reader + scanline rasterizer + PNG writer.
// No network at runtime. Deterministic: same bytes on every run.
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync } from 'node:zlib';

// ---------------------------------------------------------------- constants
const PW = 1024, PH = 1024, SS = 2;            // page px, supersample factor
const BW = PW * SS, BH = PH * SS;              // backing buffer px
const MX = 28, CW = 968;                       // content left, content width
const PAPER = '#f8f4ea', INK = '#1b1712', SOFT = '#5c564a';
const RED = '#b3271e', RED_D = '#8f1d15', RULE = '#d9cfba';
const SEA = '#cfe3f2', LAND = '#2f7d3d', LAND_D = '#1d5227';
const SKY1 = '#bcd9ee', SKY2 = '#e8d9a8';

// ---------------------------------------------------------------- colour utils
type RGB = [number, number, number];
function hex(h: string): RGB {
  const n = parseInt(h.slice(1), 16);
  return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
}
function mix(a: RGB, b: RGB, t: number): RGB {
  return [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t];
}

// ---------------------------------------------------------------- TrueType face
interface Pt { x: number; y: number; on: boolean }
interface Contour { pts: Pt[] }
interface GlyphBits { w: number; h: number; ox: number; oy: number; adv: number; a: Uint8Array }

class Face {
  private buf: Buffer;
  private upem: number;
  private nGlyphs: number;
  private hmtxOff: number; private nHmtx: number;
  private locaOff: number; private locaFmt: number;
  private glyfOff: number;
  private cmap12: { s: number; e: number; g: number }[] = [];
  private cmap4: { e: number; d: number; ro: number; sc: number[] } | null = null;
  private cmap4Base = 0;
  private cache = new Map<string, GlyphBits>();

  constructor(path: string) {
    this.buf = readFileSync(path);
    const b = this.buf;
    const u16 = (o: number) => b.readUInt16BE(o);
    const u32 = (o: number) => b.readUInt32BE(o);
    const nTab = u16(4);
    const tabs = new Map<string, number>();
    for (let i = 0; i < nTab; i++) {
      const o = 12 + i * 16;
      tabs.set(b.toString('ascii', o, o + 4), u32(o + 8));
    }
    const head = tabs.get('head')!;
    this.upem = u16(head + 18);
    this.locaFmt = b.readInt16BE(head + 50);
    this.nGlyphs = u16(tabs.get('maxp')! + 4);
    const hhea = tabs.get('hhea')!;
    this.nHmtx = u16(hhea + 34);
    this.hmtxOff = tabs.get('hmtx')!;
    this.locaOff = tabs.get('loca')!;
    this.glyfOff = tabs.get('glyf')!;
    // cmap: prefer format 12, fall back to format 4
    const cmap = tabs.get('cmap')!;
    const nSub = u16(cmap + 2);
    let f4 = -1;
    for (let i = 0; i < nSub; i++) {
      const o = cmap + 4 + i * 8;
      const sub = cmap + u32(o + 4); // subtable offsets are relative to cmap start
      const fmt = u16(sub);
      if (fmt === 12) { this.readCmap12(sub); break; }
      if (fmt === 4) f4 = sub;
    }
    if (!this.cmap12.length && f4 >= 0) this.readCmap4(f4);
  }
  private readCmap12(off: number) {
    const b = this.buf, u32 = (o: number) => b.readUInt32BE(o);
    const n = u32(off + 12);
    for (let i = 0; i < n; i++) {
      const o = off + 16 + i * 12;
      this.cmap12.push({ s: u32(o), e: u32(o + 4), g: u32(o + 8) });
    }
  }
  private readCmap4(off: number) {
    const b = this.buf, u16 = (o: number) => b.readUInt16BE(o);
    const seg2 = u16(off + 6);
    const endBase = off + 14, startBase = endBase + seg2 + 2, deltaBase = startBase + seg2, roBase = deltaBase + seg2;
    const ends: number[] = [];
    for (let i = 0; i < seg2 / 2; i++) ends.push(u16(endBase + i * 2));
    const starts: number[] = [];
    for (let i = 0; i < seg2 / 2; i++) starts.push(u16(startBase + i * 2));
    const deltas: number[] = [];
    for (let i = 0; i < seg2 / 2; i++) deltas.push(b.readInt16BE(deltaBase + i * 2));
    this.cmap4 = { e: 0, d: 0, ro: 0, sc: [] };
    (this as any).c4 = { ends, starts, deltas, roBase, off };
    this.cmap4Base = off;
  }
  glyphId(ch: number): number {
    for (const g of this.cmap12) if (ch >= g.s && ch <= g.e) return g.g + (ch - g.s);
    const c4 = (this as any).c4;
    if (c4) {
      for (let i = 0; i < c4.ends.length; i++) {
        if (ch <= c4.ends[i] && ch >= c4.starts[i]) {
          if (c4.deltas[i] !== 0 || true) {
            const ro = this.buf.readUInt16BE(c4.roBase + i * 2);
            if (ro === 0) return (ch + c4.deltas[i]) & 0xffff;
            const idx = c4.roBase + i * 2 + ro + (ch - c4.starts[i]) * 2;
            const g = this.buf.readUInt16BE(idx);
            return g === 0 ? 0 : (g + c4.deltas[i]) & 0xffff;
          }
        }
      }
    }
    return 0;
  }
  advance(gid: number): number {
    const g = Math.min(gid, this.nHmtx - 1);
    return this.buf.readUInt16BE(this.hmtxOff + g * 4);
  }
  private glyphOff(gid: number): [number, number] {
    const b = this.buf;
    let o0: number, o1: number;
    if (this.locaFmt === 0) {
      o0 = b.readUInt16BE(this.locaOff + gid * 2) * 2;
      o1 = b.readUInt16BE(this.locaOff + (gid + 1) * 2) * 2;
    } else {
      o0 = b.readUInt32BE(this.locaOff + gid * 4);
      o1 = b.readUInt32BE(this.locaOff + (gid + 1) * 4);
    }
    return [this.glyfOff + o0, o1 - o0];
  }
  // outline of a glyph as contours in font units (y up), composites expanded
  outline(gid: number): Contour[] {
    const [off, len] = this.glyphOff(gid);
    if (len <= 0) return [];
    const b = this.buf;
    const nC = b.readInt16BE(off);
    if (nC >= 0) return this.simpleOutline(off, nC);
    // composite
    let p = off + 10;
    const out: Contour[] = [];
    for (;;) {
      const flags = b.readUInt16BE(p); p += 2;
      const comp = b.readUInt16BE(p); p += 2;
      let ax = 0, ay = 0;
      if (flags & 0x0001) { ax = b.readInt16BE(p); ay = b.readInt16BE(p + 2); p += 4; }
      else { ax = b.readInt8(p); ay = b.readInt8(p + 1); p += 2; }
      let a = 1, bb = 0, c = 0, d = 1;
      if (flags & 0x0008) { const s = b.readInt16BE(p) / 16384; a = s; d = s; p += 2; }
      else if (flags & 0x0040) { a = b.readInt16BE(p) / 16384; d = b.readInt16BE(p + 2) / 16384; p += 4; }
      else if (flags & 0x0080) { a = b.readInt16BE(p) / 16384; bb = b.readInt16BE(p + 2) / 16384; c = b.readInt16BE(p + 4) / 16384; d = b.readInt16BE(p + 6) / 16384; p += 8; }
      const xy = (flags & 0x0002) !== 0;
      for (const cn of this.outline(comp)) {
        out.push({ pts: cn.pts.map((q) => ({
          x: a * q.x + c * q.y + (xy ? ax : 0),
          y: bb * q.x + d * q.y + (xy ? ay : 0),
          on: q.on,
        })) });
      }
      if (!(flags & 0x0020)) break;
    }
    return out;
  }
  private simpleOutline(off: number, nC: number): Contour[] {
    const b = this.buf;
    const ends: number[] = [];
    for (let i = 0; i < nC; i++) ends.push(b.readUInt16BE(off + 10 + i * 2));
    let p = off + 10 + nC * 2;
    const insLen = b.readUInt16BE(p); p += 2 + insLen;
    const nPts = ends.length ? ends[ends.length - 1] + 1 : 0;
    const flags: number[] = [];
    for (let i = 0; i < nPts;) {
      const f = b[p++];
      flags.push(f);
      if (f & 0x08) { const r = b[p++]; for (let k = 0; k < r; k++) flags.push(f); i += r + 1; }
      else i++;
    }
    const xs: number[] = []; let x = 0;
    for (let i = 0; i < nPts; i++) {
      const f = flags[i];
      if (f & 0x02) { const v = b[p++]; x += (f & 0x10) ? v : -v; }
      else if (!(f & 0x10)) { x += b.readInt16BE(p); p += 2; }
      xs.push(x);
    }
    const ys: number[] = []; let y = 0;
    for (let i = 0; i < nPts; i++) {
      const f = flags[i];
      if (f & 0x04) { const v = b[p++]; y += (f & 0x20) ? v : -v; }
      else if (!(f & 0x20)) { y += b.readInt16BE(p); p += 2; }
      ys.push(y);
    }
    const out: Contour[] = [];
    let start = 0;
    for (let ci = 0; ci < nC; ci++) {
      const end = ends[ci];
      const raw: Pt[] = [];
      for (let i = start; i <= end; i++) raw.push({ x: xs[i], y: ys[i], on: (flags[i] & 0x01) !== 0 });
      // expand implied on-curve midpoints between consecutive off-curve points
      const pts: Pt[] = [];
      const m = raw.length;
      for (let i = 0; i < m; i++) {
        const cur = raw[i], nxt = raw[(i + 1) % m];
        pts.push(cur);
        if (!cur.on && !nxt.on) pts.push({ x: (cur.x + nxt.x) / 2, y: (cur.y + nxt.y) / 2, on: true });
      }
      out.push({ pts });
      start = end + 1;
    }
    return out;
  }
  // rasterize one glyph at `size` px (em size) into an alpha bitmap (SS supersampled)
  glyph(ch: string, size: number): GlyphBits {
    const key = ch + '|' + size;
    const hit = this.cache.get(key);
    if (hit) return hit;
    const gid = this.glyphId(ch.codePointAt(0)!);
    const adv = (this.advance(gid) / this.upem) * size;
    const cnts = this.outline(gid);
    const sc = (size * SS) / this.upem;
    let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
    const polys: number[][][] = [];
    for (const cn of cnts) {
      const poly = flattenContour(cn, sc);
      if (poly.length < 3) continue;
      polys.push(poly);
      for (const [px, py] of poly) {
        if (px < minX) minX = px; if (px > maxX) maxX = px;
        if (py < minY) minY = py; if (py > maxY) maxY = py;
      }
    }
    if (!polys.length || !isFinite(minX)) {
      const g: GlyphBits = { w: 0, h: 0, ox: 0, oy: 0, adv, a: new Uint8Array(0) };
      this.cache.set(key, g); return g;
    }
    const x0 = Math.floor(minX), x1 = Math.ceil(maxX), y0 = Math.floor(minY), y1 = Math.ceil(maxY);
    const w = Math.max(1, x1 - x0), h = Math.max(1, y1 - y0);
    const a = new Uint8Array(w * h);
    // scanline fill, even-odd, one sample per subpixel row centre
    const shifted = polys.map((poly) => poly.map(([px, py]) => [px - x0, py - y0] as [number, number]));
    for (let r = 0; r < h; r++) {
      const sy = r + 0.5;
      const xs: number[] = [];
      for (const poly of shifted) {
        for (let i = 0; i < poly.length; i++) {
          const [ax, ay] = poly[i], [bx, by] = poly[(i + 1) % poly.length];
          if ((ay <= sy && by > sy) || (by <= sy && ay > sy)) {
            xs.push(ax + (sy - ay) * (bx - ax) / (by - ay));
          }
        }
      }
      xs.sort((p, q) => p - q);
      for (let i = 0; i + 1 < xs.length; i += 2) {
        const c0 = Math.max(0, Math.ceil(xs[i] - 0.5)), c1 = Math.min(w, Math.floor(xs[i + 1] - 0.5) + 1);
        for (let cx = c0; cx < c1; cx++) a[r * w + cx] = 255;
      }
    }
    const g: GlyphBits = { w, h, ox: x0 / SS, oy: y0 / SS, adv, a };
    this.cache.set(key, g);
    return g;
  }
  textWidth(t: string, size: number, track = 0): number {
    let w = 0;
    for (const ch of t) w += this.glyph(ch, size).adv + track;
    return w - (t.length ? track : 0);
  }
}

// flatten one contour (font units -> scaled px, y down) to a polygon
function flattenContour(cn: Contour, sc: number): [number, number][] {
  const pts = cn.pts;
  if (pts.length < 2) return [];
  const out: [number, number][] = [];
  const start = pts[0];
  let cx = start.x, cy = start.y;
  out.push([cx * sc, -cy * sc]);
  let i = 1;
  while (i < pts.length) {
    const p = pts[i];
    if (p.on) { out.push([p.x * sc, -p.y * sc]); cx = p.x; cy = p.y; i++; }
    else {
      const nxt = pts[(i + 1) % pts.length];
      const end = nxt.on ? nxt : { x: (p.x + nxt.x) / 2, y: (p.y + nxt.y) / 2, on: true };
      subQuad(cx, cy, p.x, p.y, end.x, end.y, sc, out);
      cx = end.x; cy = end.y;
      i += nxt.on ? 2 : 1;
    }
  }
  // close back to start if the last point is off-curve handled above; add start if needed
  return out;
}
function subQuad(x0: number, y0: number, x1: number, y1: number, x2: number, y2: number, sc: number, out: [number, number][]) {
  const flat = Math.abs(x0 - 2 * x1 + x2) + Math.abs(y0 - 2 * y1 + y2);
  if (flat * sc < 0.6) { out.push([x2 * sc, -y2 * sc]); return; }
  const mx01 = (x0 + x1) / 2, my01 = (y0 + y1) / 2, mx12 = (x1 + x2) / 2, my12 = (y1 + y2) / 2;
  const mx = (mx01 + mx12) / 2, my = (my01 + my12) / 2;
  subQuad(x0, y0, mx01, my01, mx, my, sc, out);
  subQuad(mx, my, mx12, my12, x2, y2, sc, out);
}

// ---------------------------------------------------------------- canvas (2x backing, RGB)
class Page {
  buf = new Uint8Array(BW * BH * 3);
  constructor() { this.fillRect(0, 0, PW, PH, hex(PAPER)); }
  private blend(ix: number, c: RGB, a: number) {
    const o = ix * 3;
    this.buf[o] = this.buf[o] * (1 - a) + c[0] * a;
    this.buf[o + 1] = this.buf[o + 1] * (1 - a) + c[1] * a;
    this.buf[o + 2] = this.buf[o + 2] * (1 - a) + c[2] * a;
  }
  fillRect(x: number, y: number, w: number, h: number, c: RGB, a = 1) {
    const x0 = Math.max(0, Math.round(x * SS)), y0 = Math.max(0, Math.round(y * SS));
    const x1 = Math.min(BW, Math.round((x + w) * SS)), y1 = Math.min(BH, Math.round((y + h) * SS));
    for (let yy = y0; yy < y1; yy++) for (let xx = x0; xx < x1; xx++) this.blend(yy * BW + xx, c, a);
  }
  // even-odd fill of one or more polygons (page coords)
  fillPoly(polys: number[][][], c: RGB, a = 1) {
    const sp = polys.map((poly) => poly.map(([px, py]) => [px * SS, py * SS] as [number, number]));
    let minY = Infinity, maxY = -Infinity;
    for (const poly of sp) for (const [, py] of poly) { if (py < minY) minY = py; if (py > maxY) maxY = py; }
    const r0 = Math.max(0, Math.floor(minY)), r1 = Math.min(BH, Math.ceil(maxY));
    for (let r = r0; r < r1; r++) {
      const sy = r + 0.5, xs: number[] = [];
      for (const poly of sp) {
        for (let i = 0; i < poly.length; i++) {
          const [ax, ay] = poly[i], [bx, by] = poly[(i + 1) % poly.length];
          if ((ay <= sy && by > sy) || (by <= sy && ay > sy)) xs.push(ax + (sy - ay) * (bx - ax) / (by - ay));
        }
      }
      xs.sort((p, q) => p - q);
      for (let i = 0; i + 1 < xs.length; i += 2) {
        const c0 = Math.max(0, Math.ceil(xs[i] - 0.5)), c1 = Math.min(BW, Math.floor(xs[i + 1] - 0.5) + 1);
        for (let xx = c0; xx < c1; xx++) this.blend(r * BW + xx, c, a);
      }
    }
  }
  circle(cx: number, cy: number, r: number, c: RGB, a = 1) {
    this.fillPoly([polyCircle(cx, cy, r, 40)], c, a);
  }
  ellipse(cx: number, cy: number, rx: number, ry: number, c: RGB, a = 1) {
    const pts: [number, number][] = [];
    for (let i = 0; i < 40; i++) { const t = (i / 40) * Math.PI * 2; pts.push([cx + Math.cos(t) * rx, cy + Math.sin(t) * ry]); }
    this.fillPoly([pts], c, a);
  }
  // thick line with round caps
  line(x0: number, y0: number, x1: number, y1: number, w: number, c: RGB, a = 1) {
    const dx = x1 - x0, dy = y1 - y0, len = Math.hypot(dx, dy) || 1;
    const nx = (-dy / len) * w / 2, ny = (dx / len) * w / 2;
    this.fillPoly([[[x0 + nx, y0 + ny], [x1 + nx, y1 + ny], [x1 - nx, y1 - ny], [x0 - nx, y0 - ny]]], c, a);
    this.circle(x0, y0, w / 2, c, a); this.circle(x1, y1, w / 2, c, a);
  }
  ring(cx: number, cy: number, r: number, w: number, c: RGB, a = 1) {
    this.fillPoly([polyCircle(cx, cy, r + w / 2, 44), polyCircle(cx, cy, r - w / 2, 44)], c, a);
  }
  // text: baseline y in page px
  text(t: string, x: number, y: number, f: Face, size: number, c: RGB, align: 'l' | 'c' | 'r' = 'l', track = 0) {
    let sx = x;
    if (align !== 'l') { const w = f.textWidth(t, size, track); sx = align === 'c' ? x - w / 2 : x - w; }
    let pen = sx;
    for (const ch of t) {
      const g = f.glyph(ch, size);
      if (g.w > 0) {
        const bx = Math.round((pen + g.ox) * SS), by = Math.round((y + g.oy) * SS);
        for (let r = 0; r < g.h; r++) {
          const yy = by + r; if (yy < 0 || yy >= BH) continue;
          for (let cc = 0; cc < g.w; cc++) {
            const av = g.a[r * g.w + cc]; if (!av) continue;
            const xx = bx + cc; if (xx < 0 || xx >= BW) continue;
            this.blend(yy * BW + xx, c, av / 255);
          }
        }
      }
      pen += g.adv + track;
    }
  }
  wrap(t: string, f: Face, size: number, maxW: number, track = 0): string[] {
    const words = t.split(' ');
    const lines: string[] = []; let cur = '';
    for (const w of words) {
      const cand = cur ? cur + ' ' + w : w;
      if (f.textWidth(cand, size, track) <= maxW || !cur) cur = cand;
      else { lines.push(cur); cur = w; }
    }
    if (cur) lines.push(cur);
    return lines;
  }
  para(t: string, x: number, y: number, f: Face, size: number, lead: number, c: RGB, maxW: number, track = 0): number {
    const lines = this.wrap(t, f, size, maxW, track);
    lines.forEach((ln, i) => this.text(ln, x, y + i * lead, f, size, c, 'l', track));
    return lines.length;
  }
  // downsample 2x -> 1x RGB, plus a whisper of deterministic print grain
  // (invisible at arm's length, keeps the flat-colour plate from over-compressing)
  toRGB(): Uint8Array {
    const out = new Uint8Array(PW * PH * 3);
    let s = 987654321;
    const rnd = () => (s = (s * 1103515245 + 12345) & 0x7fffffff) / 0x7fffffff;
    for (let y = 0; y < PH; y++) for (let x = 0; x < PW; x++) {
      const o = (y * PW + x) * 3;
      let r = 0, g = 0, b = 0;
      for (let dy = 0; dy < SS; dy++) for (let dx = 0; dx < SS; dx++) {
        const s2 = ((y * SS + dy) * BW + (x * SS + dx)) * 3;
        r += this.buf[s2]; g += this.buf[s2 + 1]; b += this.buf[s2 + 2];
      }
      const n = Math.floor(rnd() * 3) - 1;
      out[o] = Math.max(0, Math.min(255, r / 4 + n));
      out[o + 1] = Math.max(0, Math.min(255, g / 4 + n));
      out[o + 2] = Math.max(0, Math.min(255, b / 4 + n));
    }
    return out;
  }
}
function polyCircle(cx: number, cy: number, r: number, n: number): [number, number][] {
  const pts: [number, number][] = [];
  for (let i = 0; i < n; i++) { const t = (i / n) * Math.PI * 2; pts.push([cx + Math.cos(t) * r, cy + Math.sin(t) * r]); }
  return pts;
}
function star(cx: number, cy: number, r: number, rot = -Math.PI / 2): [number, number][] {
  const pts: [number, number][] = [];
  for (let i = 0; i < 10; i++) {
    const rr = i % 2 === 0 ? r : r * 0.42, t = rot + (i / 10) * Math.PI * 2;
    pts.push([cx + Math.cos(t) * rr, cy + Math.sin(t) * rr]);
  }
  return pts;
}
// deterministic grain (newsprint): tiny seeded PRNG
function grain(pg: Page) {
  let s = 20261126;
  const rnd = () => (s = (s * 1103515245 + 12345) & 0x7fffffff) / 0x7fffffff;
  for (let i = 0; i < 26000; i++) {
    const x = Math.floor(rnd() * PW), y = Math.floor(rnd() * PH);
    const v = rnd() > 0.5 ? 255 : 0;
    pg.fillRect(x, y, 1, 1, [v, v, v], 0.05);
  }
}

// ---------------------------------------------------------------- PNG writer
function crc32(buf: Buffer): number {
  let table = (crc32 as any).t as Int32Array;
  if (!table) {
    table = new Int32Array(256);
    for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; table[n] = c; }
    (crc32 as any).t = table;
  }
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) c = table[(c ^ buf[i]) & 255] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}
function chunk(type: string, data: Buffer): Buffer {
  const out = Buffer.alloc(12 + data.length);
  out.writeUInt32BE(data.length, 0);
  out.write(type, 4, 'ascii');
  data.copy(out, 8);
  out.writeUInt32BE(crc32(Buffer.concat([Buffer.from(type, 'ascii'), data])), 8 + data.length);
  return out;
}
function writePNG(rgb: Uint8Array): Buffer {
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(PW, 0); ihdr.writeUInt32BE(PH, 4);
  ihdr[8] = 8; ihdr[9] = 2; ihdr[10] = 0; ihdr[11] = 0; ihdr[12] = 0;
  const raw = Buffer.alloc(PH * (1 + PW * 3));
  for (let y = 0; y < PH; y++) {
    const row = rgb.subarray(y * PW * 3, (y + 1) * PW * 3);
    const off = y * (1 + PW * 3);
    // choose filter 0 vs Paeth by sum of |signed byte|
    let s0 = 0, sP = 0;
    for (let i = 0; i < row.length; i++) { const v = row[i]; s0 += Math.abs(v < 128 ? v : v - 256); }
    const paeth = Buffer.alloc(row.length);
    for (let i = 0; i < row.length; i++) {
      const a = i >= 3 ? row[i - 3] : 0, b = y > 0 ? rgb[(y - 1) * PW * 3 + i] : 0, c = y > 0 && i >= 3 ? rgb[(y - 1) * PW * 3 + i - 3] : 0;
      const p = a + b - c, pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c);
      const pr = pa <= pb && pa <= pc ? a : pb <= pc ? b : c;
      const v = (row[i] - pr) & 255;
      paeth[i] = v; sP += Math.abs(v < 128 ? v : v - 256);
    }
    if (sP < s0) { raw[off] = 4; paeth.copy(raw, off + 1); }
    else { raw[off] = 0; Buffer.from(row).copy(raw, off + 1); }
  }
  const idat = deflateSync(raw, { level: 9 });
  return Buffer.concat([Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]), chunk('IHDR', ihdr), chunk('IDAT', idat), chunk('IEND', Buffer.alloc(0))]);
}

// ---------------------------------------------------------------- data
const REGIONS = [
  { n: 'N. AMERICA', short: 'N. AMERICA', col: '#1d4ed8' },
  { n: 'LATIN AMERICA', short: 'LATIN AM.', col: '#15803d' },
  { n: 'EUROPE', short: 'EUROPE', col: '#6d28d9' },
  { n: 'MIDDLE EAST', short: 'MID. EAST', col: '#b91c1c' },
  { n: 'N. AFRICA', short: 'N. AFRICA', col: '#c2410c' },
  { n: 'SUB-SAHARAN AFRICA', short: 'SUB-SAH. AFR.', col: '#a16207' },
  { n: 'SOUTH ASIA', short: 'S. ASIA', col: '#be185d' },
  { n: 'EAST & SE ASIA', short: 'E. & SE ASIA', col: '#0f766e' },
  { n: 'OCEANIA', short: 'OCEANIA', col: '#0369a1' },
  { n: 'GLOBAL', short: 'GLOBAL', col: '#475569' },
];
const regionCol = (name: string) => (REGIONS.find((r) => r.n === name) || REGIONS[9]).col;

interface Story { no: number; place: string; field: string; tag: string; region: string; fields: string[]; head: string; deck: string; thumb: string }
const HEROES: Story[] = [
  { no: 1, place: 'WASHINGTON', field: 'TRADE', tag: 'OFFICIAL', region: 'N. AMERICA', fields: ['Trade', 'Economy'], head: 'US proposes tariffs of up to 20% on EU, China and 12 more', deck: 'USTR Greer announces Section 301 duties; China faces 20%, EU and Japan 15%.', thumb: 'ship' },
  { no: 2, place: 'RAS TANURA, SAUDI ARABIA', field: 'ENERGY', tag: 'REPORTED', region: 'MIDDLE EAST', fields: ['Energy', 'War'], head: 'Houthis claim strike on kingdom\u2019s largest refinery', deck: 'Fires at the 550,000-barrel-a-day plant; NASA imagery shows smoke over 600 sq km; coalition says 4 drones downed.', thumb: 'refinery' },
  { no: 3, place: 'STRAIT OF HORMUZ', field: 'WAR', tag: 'CLAIM', region: 'MIDDLE EAST', fields: ['War', 'Energy'], head: 'Two tankers hit naval mines, explode and burn', deck: 'IRGC says ships used an unauthorised route; a third tanker hit later; US tells citizens to leave Iran at once.', thumb: 'mines' },
];
const MEDIUM: Story[] = [
  { no: 4, place: 'GAZA CITY', field: 'WAR', tag: 'CONFIRMED', region: 'MIDDLE EAST', fields: ['War', 'Security'], head: 'Israel kills Hamas security chief', deck: 'Wife and two daughters also killed.', thumb: 'building' },
  { no: 5, place: 'SAMARA, RUSSIA', field: 'WAR', tag: 'REPORTED', region: 'EUROPE', fields: ['War', 'Energy'], head: 'Ukraine hits Russian refineries', deck: 'Fires at Syzran and Kuibyshev.', thumb: 'refinery' },
  { no: 6, place: 'DAMAZIN, SUDAN', field: 'WAR', tag: 'REPORTED', region: 'SUB-SAHARAN AFRICA', fields: ['War', 'Humanitarian'], head: 'RSF drones kill 19 in Blue Nile', deck: 'Six women dead; 20 wounded.', thumb: 'drone' },
  { no: 7, place: 'CAIRO', field: 'DISASTER', tag: 'CONFIRMED', region: 'N. AFRICA', fields: ['Disaster'], head: 'Tanker crash sets Ring Road ablaze', deck: '30 dead; 25 injured on the Ring Road.', thumb: 'tanker' },
  { no: 8, place: 'PYONGYANG', field: 'DIPLOMACY', tag: 'OFFICIAL', region: 'EAST & SE ASIA', fields: ['Diplomacy', 'Politics'], head: 'North Korea expels Swiss envoy', deck: 'Shuts office; envoy given 48 hours.', thumb: 'flag' },
  { no: 9, place: 'BENGHAZI, LIBYA', field: 'WAR', tag: 'REPORTED', region: 'N. AFRICA', fields: ['War', 'Security'], head: 'Officers die in warship strike', deck: 'Sea drones hit corvette Merkury.', thumb: 'warship' },
  { no: 10, place: 'BOGOR, INDONESIA', field: 'DISASTER', tag: 'CONFIRMED', region: 'EAST & SE ASIA', fields: ['Disaster', 'Labour'], head: 'Nine dead in gold mine', deck: '17 trapped; bodies from 100-metre pit.', thumb: 'minepit' },
  { no: 11, place: 'MISSISSIPPI, US', field: 'DISASTER', tag: 'CONFIRMED', region: 'N. AMERICA', fields: ['Disaster'], head: 'Six dead as plane crashes off coast', deck: 'Two children among the dead.', thumb: 'plane' },
  { no: 12, place: 'COLOMBIA', field: 'CRIME', tag: 'CONFIRMED', region: 'LATIN AMERICA', fields: ['Crime', 'Security'], head: 'Police free 20 hostages', deck: 'All safe after supermarket storming.', thumb: 'shop' },
  { no: 13, place: 'DHAKA', field: 'LABOUR', tag: 'OFFICIAL', region: 'SOUTH ASIA', fields: ['Labour', 'Economy'], head: 'Garment workers win wage rise', deck: '12,500 to 17,500 taka, up 36%.', thumb: 'sewing' },
];
// [no, text, region, field]
const MORE: [number, string, string, string][] = [
  [14, 'Solomon Islands: Australia security pact', 'OCEANIA', 'Diplomacy'],
  [15, 'India: 18 years since 26/11 Mumbai attacks', 'SOUTH ASIA', 'Security'],
  [16, 'Malaysia: sues Google for $146M over YouTube', 'EAST & SE ASIA', 'Justice'],
  [17, 'Lebanon: plans a second airport at Kleiat', 'MIDDLE EAST', 'Business'],
  [18, 'South Africa: Ramaphosa wins cash-theft case', 'SUB-SAHARAN AFRICA', 'Justice'],
  [19, 'UK: military jets moved over drone threats', 'EUROPE', 'Security'],
  [20, 'China: Xi probe targets Shanghai rising star', 'EAST & SE ASIA', 'Politics'],
  [21, 'Russia: ~500,000 war dead, own figures say', 'EUROPE', 'War'],
  [22, 'UK: Duran Duran\u2019s Andy Taylor dies at 65', 'EUROPE', 'Business'],
  [23, 'Brazil: Wolbachia mosquitoes cut cases 68%', 'LATIN AMERICA', 'Science'],
  [24, 'Space: ESA\u2019s Hera finds DART impact crater', 'GLOBAL', 'Space'],
  [25, 'India: Sooryavanshi, 15, hits 204 off 53', 'SOUTH ASIA', 'Sport'],
  [26, 'Geneva: Gukesh draws Game 2 vs Sindarov', 'EUROPE', 'Sport'],
  [27, 'India: Flipkart CEO to step down in December', 'SOUTH ASIA', 'Business'],
  [28, 'Cricket: 1,220 register for IPL 2027 auction', 'SOUTH ASIA', 'Sport'],
  [29, 'US: Tempus to buy Personalis in $600M deal', 'N. AMERICA', 'Business'],
  [30, 'US: AG dodges questions on Nvidia inquiry', 'N. AMERICA', 'Tech'],
  [31, 'Gaza: displaced fear violence near camps', 'MIDDLE EAST', 'Humanitarian'],
  [32, 'India: IITs add 6,000 seats in robotics, AI', 'SOUTH ASIA', 'Tech'],
  [33, 'India: Rs 15,000-crore package for Nepal', 'SOUTH ASIA', 'Diplomacy'],
  [34, 'India: calls for human control of AI in war', 'SOUTH ASIA', 'Diplomacy'],
  [35, 'Emirates tops global airline rankings', 'MIDDLE EAST', 'Business'],
  [36, 'Colombia: UN chief hails decade of peace', 'LATIN AMERICA', 'Diplomacy'],
  [37, 'Thailand: emergency plan on arsenic in rivers', 'EAST & SE ASIA', 'Environment'],
  [38, 'Nigeria: bandits kill 6 in Niger State village', 'SUB-SAHARAN AFRICA', 'Crime'],
  [39, 'Uganda: army chief says $3bn rail deal is off', 'SUB-SAHARAN AFRICA', 'Economy'],
  [40, 'US: Trump backs a 10% credit card rate cap', 'N. AMERICA', 'Economy'],
  [41, 'US: Trump confirms hack of FBI crime database', 'N. AMERICA', 'Crime'],
  [42, 'Florida: St. Johns River tops its 1953 record', 'N. AMERICA', 'Climate'],
  [43, 'Pacific: charity swaps tuition for coconuts', 'OCEANIA', 'Humanitarian'],
  [44, 'World: 16 days of action vs violence on women', 'GLOBAL', 'Rights'],
  [45, 'Lisbon: Sporting draw 2-2 with Man United', 'EUROPE', 'Sport'],
  [46, 'Zimbabwe: storms kill 10, hit 10 towns', 'SUB-SAHARAN AFRICA', 'Disaster'],
  [47, 'US: FCC clears SpaceX 1M orbital data centres', 'N. AMERICA', 'Tech'],
  [48, 'New York: Dow +0.3%, Nasdaq -0.6%', 'N. AMERICA', 'Markets'],
  [49, 'Karachi: building collapse kills 3, injures 14', 'SOUTH ASIA', 'Disaster'],
  [50, 'Brazil: storms kill 6 in Parana state', 'LATIN AMERICA', 'Disaster'],
];
const UTC: [string, string][] = [
  ['04:50', 'US tariffs'], ['06:45', 'Ukraine hits refineries'],
  ['09:46', 'Tankers hit mines'], ['13:51', 'Hamas chief killed'],
  ['17:35', 'Ras Tanura claimed'], ['20:40', 'Cairo fire kills 30'],
];
const STATS: [string, string][] = [
  ['20%', 'top proposed US tariff'], ['+2.4%', 'Brent to $93.60'],
  ['30', 'killed in Cairo tanker fire'], ['19', 'killed in Sudan drone strikes'],
  ['9', 'dead in Java gold mine'],
];
const ALL = [...HEROES, ...MEDIUM];
const regionCount = new Map<string, number>();
const fieldCount = new Map<string, number>();
for (const s of ALL) {
  regionCount.set(s.region, (regionCount.get(s.region) ?? 0) + 1);
  for (const f of s.fields) fieldCount.set(f, (fieldCount.get(f) ?? 0) + 1);
}
for (const [, , rg, fd] of MORE) {
  regionCount.set(rg, (regionCount.get(rg) ?? 0) + 1);
  fieldCount.set(fd, (fieldCount.get(fd) ?? 0) + 1);
}

// ---------------------------------------------------------------- scene helpers
function sun(pg: Page, x: number, y: number, r: number) {
  pg.circle(x, y, r, hex('#f2b53c'));
  for (let i = 0; i < 8; i++) {
    const t = (i / 8) * Math.PI * 2;
    pg.line(x + Math.cos(t) * (r + 3), y + Math.sin(t) * (r + 3), x + Math.cos(t) * (r + 9), y + Math.sin(t) * (r + 9), 2.5, hex('#f2b53c'));
  }
}
function waves(pg: Page, x: number, y: number, w: number, col: string, amp = 3) {
  const c = hex(col);
  for (let row = 0; row < 3; row++) {
    const pts: [number, number][] = [];
    for (let i = 0; i <= 40; i++) pts.push([x + (i / 40) * w, y + row * 7 + Math.sin((i / 40) * Math.PI * 4 + row) * amp]);
    for (let i = 0; i < pts.length - 1; i++) pg.line(pts[i][0], pts[i][1], pts[i + 1][0], pts[i + 1][1], 1.6, c, 0.85);
  }
}
function flame(pg: Page, x: number, y: number, s: number) {
  // teardrop flame: outer orange, inner yellow
  const outer: [number, number][] = [
    [x, y - 16 * s], [x + 7 * s, y - 6 * s], [x + 9 * s, y + 2 * s], [x + 5 * s, y + 9 * s],
    [x, y + 11 * s], [x - 5 * s, y + 9 * s], [x - 9 * s, y + 2 * s], [x - 7 * s, y - 6 * s],
  ];
  pg.fillPoly([outer], hex('#e85d04'));
  const inner: [number, number][] = [
    [x, y - 8 * s], [x + 4 * s, y - 1 * s], [x + 5 * s, y + 5 * s], [x, y + 8 * s],
    [x - 5 * s, y + 5 * s], [x - 4 * s, y - 1 * s],
  ];
  pg.fillPoly([inner], hex('#ffd60a'));
}
function smoke(pg: Page, x: number, y: number, puffs: number, drift: number, sp = 13) {
  for (let i = 0; i < puffs; i++) {
    const yy = y - i * sp, xx = x + i * drift;
    pg.circle(xx, yy, 11 - i * 0.8, hex('#3a3a38'), 0.88);
    pg.circle(xx - 5, yy + 3, 7, hex('#55524e'), 0.8);
  }
}
function seaMine(pg: Page, x: number, y: number, r: number) {
  // unmistakable naval mine: black spiked ball + chain + anchor + ripples
  const c = hex('#141414');
  for (let i = 0; i < 10; i++) {
    const t = (i / 10) * Math.PI * 2 - Math.PI / 2;
    const bx = x + Math.cos(t) * r * 0.82, by = y + Math.sin(t) * r * 0.82;
    const tx = x + Math.cos(t) * r * 1.42, ty = y + Math.sin(t) * r * 1.42;
    const px = x + Math.cos(t + 0.22) * r * 0.8, py = y + Math.sin(t + 0.22) * r * 0.8;
    const qx = x + Math.cos(t - 0.22) * r * 0.8, qy = y + Math.sin(t - 0.22) * r * 0.8;
    pg.fillPoly([[[tx, ty], [px, py], [qx, qy]]], c);
    pg.circle(bx, by, r * 0.13, c);
  }
  pg.circle(x, y, r, c);
  pg.circle(x - r * 0.32, y - r * 0.34, r * 0.28, hex('#3d3d3d'));
  // short chain down to a small anchor (kept compact so it stays in-scene)
  pg.line(x, y + r * 0.95, x, y + r * 1.25, 3, c);
  pg.fillPoly([[[x - 7, y + r * 1.25], [x + 7, y + r * 1.25], [x + 4, y + r * 1.5], [x - 4, y + r * 1.5]]], c);
  pg.fillPoly([[[x - 11, y + r * 1.3], [x - 3, y + r * 1.42], [x - 9, y + r * 1.52]]], c);
  pg.fillPoly([[[x + 11, y + r * 1.3], [x + 3, y + r * 1.42], [x + 9, y + r * 1.52]]], c);
  // ripples on the waterline
  pg.ring(x, y + r * 0.9, r * 1.35, 1.6, hex('#ffffff'), 0.9);
  pg.ring(x, y + r * 0.9, r * 1.75, 1.4, hex('#ffffff'), 0.55);
}
function tanker(pg: Page, x: number, y: number, w: number, h: number, col: string, list = 0) {
  const c = hex(col), dark = hex('#22303c');
  const hull: [number, number][] = [
    [x, y], [x + w, y], [x + w - 8, y + h], [x + 10, y + h],
  ];
  pg.fillPoly([hull], dark);
  pg.fillRect(x + 6, y - h * 0.55, w - 14, h * 0.55, c);
  pg.fillRect(x + w * 0.62, y - h * 1.05, w * 0.2, h * 0.5, hex('#f4f1e6'));
  pg.fillRect(x + w * 0.62, y - h * 1.25, w * 0.2, h * 0.2, hex('#c0392b'));
  pg.fillRect(x + 10, y - h * 0.42, w * 0.42, h * 0.42, hex('#7a1f1a'));
  if (list) { /* hull drawn level; list shown by flame/smoke instead */ }
}
function flagEU(pg: Page, x: number, y: number, w: number, h: number) {
  pg.fillRect(x, y, w, h, hex('#1e3a8a'));
  for (let i = 0; i < 12; i++) {
    const t = (i / 12) * Math.PI * 2 - Math.PI / 2;
    pg.circle(x + w / 2 + Math.cos(t) * w * 0.28, y + h / 2 + Math.sin(t) * h * 0.28, 1.6, hex('#ffd60a'));
  }
}
function flagCN(pg: Page, x: number, y: number, w: number, h: number) {
  pg.fillRect(x, y, w, h, hex('#de2910'));
  pg.fillPoly([star(x + w * 0.22, y + h * 0.3, 4.5)], hex('#ffde00'));
  pg.fillPoly([star(x + w * 0.62, y + h * 0.22, 2)], hex('#ffde00'));
  pg.fillPoly([star(x + w * 0.72, y + h * 0.42, 2)], hex('#ffde00'));
  pg.fillPoly([star(x + w * 0.62, y + h * 0.62, 2)], hex('#ffde00'));
  pg.fillPoly([star(x + w * 0.45, y + h * 0.68, 2)], hex('#ffde00'));
}

// hero scenes (scene box x,y,w,h = 312x130)
function sceneShip(pg: Page, x: number, y: number, w: number, h: number) {
  pg.fillRect(x, y, w, h * 0.62, hex(SKY1));
  pg.fillRect(x, y + h * 0.62, w, h * 0.38, hex('#2e6f9e'));
  sun(pg, x + w - 42, y + 26, 15);
  // flag poles
  pg.line(x + 18, y + 12, x + 18, y + 52, 2, hex('#5c564a'));
  flagEU(pg, x + 18, y + 12, 26, 17);
  pg.line(x + w - 46, y + 12, x + w - 46, y + 52, 2, hex('#5c564a'));
  flagCN(pg, x + w - 46, y + 12, 26, 17);
  // container ship
  const sy = y + h * 0.62;
  pg.fillPoly([[[x + 30, sy - 6], [x + w - 24, sy - 6], [x + w - 40, sy + 22], [x + 44, sy + 22]]], hex('#22303c'));
  const contCols = ['#1e3a8a', '#de2910', '#f2b53c', '#15803d', '#b91c1c', '#0369a1'];
  for (let r = 0; r < 2; r++) for (let i = 0; i < 6; i++) {
    pg.fillRect(x + 52 + i * 32, sy - 34 - r * 15, 30, 13, hex(contCols[(i + r) % 6]));
    pg.fillRect(x + 52 + i * 32, sy - 34 - r * 15, 30, 2, hex('#000000'), 0.25);
  }
  pg.fillRect(x + w - 62, sy - 58, 26, 24, hex('#f4f1e6'));
  pg.fillRect(x + w - 62, sy - 66, 26, 8, hex('#c0392b'));
  waves(pg, x + 8, sy + 26, w - 16, '#ffffff', 2.5);
  // stamp UP TO 20% — bottom-left over open water, clear of ship and flags
  const cx = x + 58, cy = sy + 30, ang = -0.14;
  const rw = 92, rh = 26;
  const rot = (dx: number, dy: number): [number, number] => [cx + dx * Math.cos(ang) - dy * Math.sin(ang), cy + dx * Math.sin(ang) + dy * Math.cos(ang)];
  const outer = [rot(-rw / 2, -rh / 2), rot(rw / 2, -rh / 2), rot(rw / 2, rh / 2), rot(-rw / 2, rh / 2)];
  pg.fillPoly([outer], hex(RED), 0.94);
  pg.text('UP TO 20%', cx, cy + 5, F_BOLD, 13, hex('#ffffff'), 'c', 0.5);
}
function sceneRefinery(pg: Page, x: number, y: number, w: number, h: number) {
  pg.fillRect(x, y, w, h * 0.66, hex('#f2a65e'));
  pg.fillRect(x, y + h * 0.66, w, h * 0.34, hex('#5a4632'));
  sun(pg, x + 52, y + 28, 16);
  // storage tanks
  pg.ellipse(x + 52, y + h * 0.66, 26, 7, hex('#e8e2d2'));
  pg.fillRect(x + 26, y + h * 0.66, 52, 22, hex('#e8e2d2'));
  pg.ellipse(x + 52, y + h * 0.66 + 22, 26, 7, hex('#cfc8b4'));
  pg.ellipse(x + 258, y + h * 0.66, 22, 6, hex('#ddd5c0'));
  pg.fillRect(x + 236, y + h * 0.66, 44, 18, hex('#ddd5c0'));
  // two refinery towers (shorter, so flames + smoke stay inside the scene)
  pg.fillRect(x + 128, y + 40, 18, h * 0.66 - 40, hex('#6b7280'));
  pg.fillRect(x + 168, y + 30, 18, h * 0.66 - 30, hex('#4b5563'));
  pg.fillRect(x + 122, y + 52, 30, 4, hex('#374151'));
  pg.fillRect(x + 162, y + 42, 30, 4, hex('#374151'));
  pg.fillRect(x + 122, y + 66, 30, 4, hex('#374151'));
  pg.fillRect(x + 162, y + 58, 30, 4, hex('#374151'));
  pg.fillRect(x + 128, y + 34, 18, 6, hex('#374151'));
  pg.fillRect(x + 168, y + 24, 18, 6, hex('#374151'));
  // pipes between towers
  pg.line(x + 146, y + 58, x + 168, y + 52, 4, hex('#374151'));
  // flames at tower tops and base
  flame(pg, x + 137, y + 34, 1.1);
  flame(pg, x + 177, y + 26, 1.2);
  flame(pg, x + 205, y + h * 0.66 - 6, 1.4);
  flame(pg, x + 108, y + h * 0.66 - 4, 1.0);
  // black smoke columns, rising from the flames, clamped inside the scene box
  smoke(pg, x + 137, y + 30, 3, 3, 8);
  smoke(pg, x + 177, y + 22, 3, 4, 7);
  // drone silhouette
  pg.ellipse(x + 252, y + 22, 9, 4, hex('#141414'));
  pg.line(x + 240, y + 18, x + 264, y + 18, 2, hex('#141414'));
  pg.line(x + 243, y + 26, x + 238, y + 34, 1.6, hex('#141414'));
  pg.line(x + 261, y + 26, x + 266, y + 34, 1.6, hex('#141414'));
}
function sceneMines(pg: Page, x: number, y: number, w: number, h: number) {
  pg.fillRect(x, y, w, h * 0.55, hex('#fbe3b0'));
  pg.fillRect(x, y + h * 0.55, w, h * 0.45, hex('#2b6a8f'));
  sun(pg, x + 44, y + 26, 15);
  // tanker left, burning
  tanker(pg, x + 14, y + h * 0.55 + 6, 120, 16, '#7a1f1a');
  flame(pg, x + 46, y + h * 0.55 - 2, 1.3);
  flame(pg, x + 96, y + h * 0.55 + 2, 1.0);
  smoke(pg, x + 46, y + h * 0.55 - 12, 4, 3);
  // tanker right
  tanker(pg, x + 178, y + h * 0.55 + 14, 118, 15, '#8a5a2b');
  flame(pg, x + 236, y + h * 0.55 + 6, 1.1);
  smoke(pg, x + 236, y + h * 0.55 - 4, 3, -3);
  // small mine mid-water (chain + anchor kept inside the scene box)
  seaMine(pg, x + 232, y + h * 0.55 + 28, 12);
  // BIG mine front and centre — ball 56 px across, 10 spikes, chain + anchor
  seaMine(pg, x + 128, y + h * 0.55 + 11, 28);
  waves(pg, x + 8, y + h - 12, w - 16, '#ffffff', 2.5);
}

// medium thumbnails (54x54 box)
function thumb(pg: Page, kind: string, x: number, y: number, s: number) {
  const bg: Record<string, string> = {
    building: '#e8dcc8', refinery: '#f2c98f', drone: '#dfe8ef', tanker: '#e8dcc8',
    flag: '#dfe8ef', warship: '#cfe3f2', minepit: '#e0d3b8', plane: '#cfe3f2',
    shop: '#e3d9f2', sewing: '#f2ddd3',
  };
  pg.fillRect(x, y, s, s, hex(bg[kind] || '#e8e8e8'));
  pg.fillRect(x, y, s, 3, hex('#1b1712'), 0.85);
  const dk = hex('#1b1712');
  if (kind === 'building') {
    pg.fillRect(x + 10, y + 18, 22, 28, hex('#8a7d68'));
    pg.fillRect(x + 32, y + 26, 12, 20, hex('#a89a80'));
    pg.fillRect(x + 14, y + 24, 4, 5, hex('#f2b53c')); pg.fillRect(x + 22, y + 24, 4, 5, hex('#f2b53c'));
    smoke(pg, x + 20, y + 12, 3, 2);
  } else if (kind === 'refinery') {
    pg.fillRect(x + 12, y + 16, 8, 30, hex('#6b7280'));
    pg.fillRect(x + 28, y + 10, 8, 36, hex('#4b5563'));
    flame(pg, x + 16, y + 10, 0.8); flame(pg, x + 32, y + 4, 0.9);
    pg.ellipse(x + 44, y + 40, 7, 3, hex('#e8e2d2')); pg.fillRect(x + 37, y + 40, 14, 6, hex('#e8e2d2'));
  } else if (kind === 'drone') {
    pg.ellipse(x + 27, y + 14, 8, 3.5, dk);
    pg.line(x + 16, y + 11, x + 38, y + 11, 1.6, dk);
    pg.line(x + 20, y + 17, x + 16, y + 24, 1.4, dk); pg.line(x + 34, y + 17, x + 38, y + 24, 1.4, dk);
    pg.fillRect(x + 8, y + 34, 12, 12, hex('#a89a80')); pg.fillRect(x + 24, y + 38, 12, 8, hex('#8a7d68'));
    pg.fillRect(x + 40, y + 34, 10, 12, hex('#a89a80'));
  } else if (kind === 'tanker') {
    pg.fillRect(x + 6, y + 38, 42, 4, hex('#5c564a'));
    pg.fillRect(x + 10, y + 22, 26, 12, hex('#c0392b'));
    pg.ellipse(x + 23, y + 22, 13, 4, hex('#e8e2d2'));
    pg.circle(x + 16, y + 38, 4, dk); pg.circle(x + 40, y + 38, 4, dk);
    flame(pg, x + 23, y + 16, 0.9);
  } else if (kind === 'flag') {
    pg.line(x + 14, y + 8, x + 14, y + 46, 2, dk);
    flagEU(pg, x + 14, y + 8, 20, 13);
    pg.fillRect(x + 30, y + 30, 16, 16, hex('#8a7d68'));
    pg.fillRect(x + 28, y + 28, 20, 3, hex('#5c564a'));
  } else if (kind === 'warship') {
    pg.fillRect(x + 4, y + 40, 46, 5, hex('#2b6a8f'));
    pg.fillPoly([[[x + 10, y + 40], [x + 44, y + 40], [x + 40, y + 32], [x + 16, y + 32]]], hex('#374151'));
    pg.fillRect(x + 30, y + 24, 4, 8, hex('#374151'));
    pg.ellipse(x + 20, y + 16, 5, 2.5, dk);
    pg.line(x + 14, y + 14, x + 26, y + 14, 1.4, dk);
  } else if (kind === 'minepit') {
    pg.ellipse(x + 27, y + 34, 16, 8, hex('#5a4632'));
    pg.ellipse(x + 27, y + 33, 12, 5, hex('#1b1712'));
    pg.circle(x + 14, y + 44, 4, hex('#8a7d68')); pg.circle(x + 40, y + 45, 3.5, hex('#8a7d68'));
    pg.fillPoly([[[x + 20, y + 14], [x + 34, y + 14], [x + 30, y + 20], [x + 24, y + 20]]], hex('#f2b53c'));
    pg.fillRect(x + 24, y + 20, 6, 3, hex('#f2b53c'));
  } else if (kind === 'plane') {
    pg.fillPoly([[[x + 6, y + 22], [x + 46, y + 18], [x + 48, y + 22], [x + 20, y + 28], [x + 10, y + 28]]], hex('#374151'));
    pg.fillPoly([[[x + 24, y + 20], [x + 30, y + 12], [x + 34, y + 20]]], hex('#374151'));
    waves(pg, x + 6, y + 42, 42, '#2b6a8f', 2);
  } else if (kind === 'shop') {
    pg.fillRect(x + 8, y + 20, 38, 24, hex('#f4f1e6'));
    pg.fillRect(x + 8, y + 14, 38, 6, hex('#7c3aed'));
    pg.fillRect(x + 12, y + 26, 10, 8, hex('#b91c1c')); pg.fillRect(x + 26, y + 26, 10, 8, hex('#15803d'));
    pg.circle(x + 40, y + 12, 9, hex('#15803d'));
    pg.fillPoly([[[x + 36, y + 12], [x + 39, y + 15], [x + 44, y + 9], [x + 44, y + 12], [x + 39, y + 18], [x + 36, y + 15]]], hex('#ffffff'));
  } else if (kind === 'sewing') {
    pg.fillRect(x + 10, y + 34, 34, 4, hex('#5c564a'));
    pg.fillPoly([[[x + 14, y + 34], [x + 20, y + 22], [x + 34, y + 22], [x + 38, y + 34]]], hex('#374151'));
    pg.fillRect(x + 36, y + 14, 3, 12, hex('#374151'));
    pg.fillRect(x + 12, y + 42, 30, 3, hex('#b91c1c'));
    pg.circle(x + 42, y + 12, 6, hex('#f2b53c'));
    pg.text('$', x + 42, y + 16, F_SANS, 9, hex('#1b1712'), 'c');
  }
}

// ---------------------------------------------------------------- world map
const CONTINENTS: number[][][] = [
  // North America
  [[-168, 66], [-150, 70], [-135, 69], [-125, 71], [-112, 68], [-100, 69], [-90, 68], [-85, 66], [-80, 62], [-76, 58], [-68, 58], [-60, 55], [-55, 47], [-60, 44], [-68, 44], [-74, 39], [-76, 35], [-80, 32], [-81, 26], [-84, 30], [-89, 29], [-95, 29], [-97, 26], [-97, 17], [-93, 15], [-88, 13], [-83, 9], [-79, 9], [-85, 11], [-90, 14], [-95, 16], [-101, 18], [-105, 20], [-110, 23], [-114, 28], [-117, 33], [-122, 37], [-124, 43], [-124, 49], [-130, 55], [-140, 60], [-152, 58], [-162, 58], [-168, 66]],
  // Greenland
  [[-45, 60], [-40, 64], [-32, 68], [-24, 70], [-20, 70], [-24, 75], [-32, 77], [-45, 76], [-55, 74], [-58, 70], [-54, 64], [-49, 60], [-45, 60]],
  // South America
  [[-79, 9], [-77, 4], [-80, -3], [-81, -6], [-77, -12], [-71, -18], [-70, -23], [-70, -30], [-72, -37], [-73, -44], [-74, -50], [-69, -54], [-66, -55], [-65, -50], [-61, -44], [-58, -38], [-52, -33], [-48, -28], [-41, -23], [-39, -17], [-35, -9], [-35, -6], [-40, -3], [-44, -2], [-50, 0], [-52, 4], [-55, 6], [-60, 8], [-63, 10], [-68, 11], [-72, 12], [-76, 10], [-79, 9]],
  // Europe
  [[-10, 36], [-9, 43], [-2, 44], [-1, 48], [0, 50], [3, 53], [8, 55], [10, 57], [18, 59], [21, 62], [25, 65], [30, 68], [32, 70], [40, 68], [44, 66], [40, 62], [35, 58], [30, 60], [24, 59], [21, 55], [19, 54], [14, 54], [10, 54], [8, 57], [5, 58], [5, 60], [10, 62], [12, 65], [18, 69], [25, 71], [30, 70], [28, 66], [24, 64], [21, 60], [18, 56], [21, 55], [24, 58], [28, 59], [30, 60], [24, 62], [19, 60], [15, 58], [12, 56], [8, 55], [5, 53], [2, 51], [0, 46], [-2, 43], [-6, 40], [-9, 37], [-10, 36]],
  // Africa
  [[-6, 35], [-10, 31], [-15, 27], [-17, 21], [-17, 15], [-16, 12], [-13, 8], [-8, 5], [-4, 5], [2, 6], [6, 4], [9, 4], [13, 0], [12, -5], [13, -10], [12, -17], [14, -22], [16, -28], [19, -34], [25, -34], [28, -32], [32, -28], [35, -24], [36, -20], [40, -15], [40, -10], [41, -4], [44, -1], [46, 2], [51, 11], [51, 12], [48, 11], [44, 13], [42, 15], [40, 15], [38, 18], [37, 20], [35, 22], [34, 27], [32, 31], [30, 32], [25, 32], [20, 32], [15, 32], [11, 34], [10, 37], [5, 37], [0, 36], [-6, 35]],
  // Asia
  [[30, 70], [40, 68], [50, 69], [60, 69], [70, 72], [80, 73], [90, 75], [100, 76], [110, 76], [120, 73], [130, 72], [140, 72], [150, 70], [160, 69], [170, 66], [178, 65], [170, 60], [162, 56], [158, 51], [156, 44], [150, 42], [142, 40], [140, 35], [135, 33], [130, 31], [127, 33], [126, 38], [122, 38], [120, 32], [122, 28], [118, 25], [110, 20], [108, 18], [105, 10], [103, 8], [100, 7], [98, 12], [95, 16], [92, 21], [90, 22], [88, 21], [86, 20], [83, 18], [80, 15], [77, 8], [75, 12], [72, 20], [70, 22], [66, 25], [62, 25], [58, 25], [56, 26], [54, 26], [52, 28], [50, 29], [48, 30], [46, 29], [43, 29], [41, 29], [39, 32], [36, 36], [34, 36], [30, 36], [28, 38], [30, 42], [33, 45], [35, 48], [38, 50], [40, 52], [42, 55], [45, 58], [48, 60], [50, 62], [45, 64], [40, 66], [35, 68], [30, 70]],
  // Australia
  [[113, -22], [114, -30], [115, -33], [118, -35], [124, -33], [129, -32], [132, -32], [135, -35], [138, -35], [140, -38], [145, -38], [150, -37], [153, -32], [153, -27], [150, -23], [146, -19], [142, -15], [142, -11], [137, -12], [135, -15], [132, -12], [130, -13], [126, -14], [122, -17], [118, -20], [113, -22]],
  // New Guinea
  [[131, -1], [136, -2], [141, -3], [146, -6], [150, -9], [146, -8], [142, -8], [138, -8], [134, -4], [131, -1]],
  // New Zealand
  [[167, -45], [170, -43], [173, -41], [175, -38], [177, -38], [174, -41], [172, -43], [168, -46], [167, -45]],
];
interface MapDot { no: number; lon: number; lat: number; region: string; label?: string; dx?: number; dy?: number }
const DOTS: MapDot[] = [
  { no: 1, lon: -77, lat: 39, region: 'N. AMERICA' },
  { no: 2, lon: 50, lat: 26.6, region: 'MIDDLE EAST', label: 'RAS TANURA', dx: 300, dy: 798 },
  { no: 3, lon: 56.5, lat: 26.5, region: 'MIDDLE EAST', label: 'HORMUZ', dx: 318, dy: 738 },
  { no: 4, lon: 34.5, lat: 31.5, region: 'MIDDLE EAST', label: 'GAZA', dx: 238, dy: 736 },
  { no: 5, lon: 50, lat: 53.2, region: 'EUROPE' },
  { no: 6, lon: 34.2, lat: 11.8, region: 'SUB-SAHARAN AFRICA' },
  { no: 7, lon: 31.2, lat: 30, region: 'N. AFRICA' },
  { no: 8, lon: 125.8, lat: 39, region: 'EAST & SE ASIA' },
  { no: 9, lon: 20.1, lat: 32.1, region: 'N. AFRICA' },
  { no: 10, lon: 106.8, lat: -6.6, region: 'EAST & SE ASIA' },
  { no: 11, lon: -89, lat: 30.3, region: 'N. AMERICA' },
  { no: 12, lon: -74, lat: 4.6, region: 'LATIN AMERICA' },
  { no: 13, lon: 90.4, lat: 23.8, region: 'SOUTH ASIA' },
];

// ---------------------------------------------------------------- fonts (loaded in main)
let F_SERIF!: Face, F_ITALIC!: Face, F_SANS!: Face, F_BOLD!: Face;

// ---------------------------------------------------------------- layout
function tagChip(pg: Page, x: number, y: number, tag: string) {
  const col = tag === 'CONFIRMED' ? '#15803d' : tag === 'OFFICIAL' ? '#1d4ed8' : tag === 'REPORTED' ? '#a16207' : '#b91c1c';
  const w = F_BOLD.textWidth(tag, 9, 0.6) + 10;
  pg.fillRect(x, y, w, 13, hex(col));
  pg.text(tag, x + 5, y + 10, F_BOLD, 9, hex('#ffffff'), 'l', 0.6);
}
function numDisc(pg: Page, cx: number, cy: number, d: number, n: number, col: string, size = 11) {
  pg.circle(cx, cy, d / 2, hex(col));
  pg.ring(cx, cy, d / 2, 1.2, hex('#ffffff'), 0.9);
  pg.text(String(n), cx, cy + size * 0.36, F_BOLD, size, hex('#ffffff'), 'c');
}
function kicker(pg: Page, x: number, y: number, s: Story) {
  pg.fillRect(x, y, 3, 11, hex(regionCol(s.region)));
  pg.text(s.place, x + 7, y + 10, F_BOLD, 10, hex(INK), 'l', 0.4);
  const afterPlace = x + 7 + F_BOLD.textWidth(s.place, 10, 0.4) + 5;
  pg.text('\u00b7 ' + s.field, afterPlace, y + 10, F_BOLD, 10, hex(RED), 'l', 0.4);
  tagChip(pg, afterPlace + F_BOLD.textWidth('\u00b7 ' + s.field, 10, 0.4) + 8, y, s.tag);
}

function main() {
  const here = new URL('.', import.meta.url).pathname;
  F_SERIF = new Face(join(here, 'fonts', 'serif-bold.ttf'));
  F_ITALIC = new Face(join(here, 'fonts', 'serif-italic.ttf'));
  F_SANS = new Face(join(here, 'fonts', 'sans.ttf'));
  F_BOLD = new Face(join(here, 'fonts', 'sans-bold.ttf'));

  const pg = new Page();
  const ink = hex(INK), soft = hex(SOFT), red = hex(RED);

  // ---- eyebrow
  pg.text('THE WORLD IN ONE DAY', MX, 24, F_BOLD, 12, red, 'l', 1.2);
  pg.text('50 STORIES \u00b7 10 REGIONS \u00b7 21 FIELDS \u00b7 ALL FIRST REPORTED ON THURSDAY 26 NOVEMBER 2026', MX + CW, 24, F_SANS, 10, soft, 'r');
  // ---- masthead + deck
  pg.text('Thursday 26 November 2026', PW / 2, 72, F_SERIF, 44, ink, 'c');
  pg.text('US proposes tariffs on 14 economies \u00b7 Houthis hit Ras Tanura refinery \u00b7 Tankers strike mines in Hormuz', PW / 2, 94, F_ITALIC, 15, red, 'c');
  pg.fillRect(MX, 100, CW, 2, hex('#1b1712'));
  pg.fillRect(MX, 103, CW, 1, hex(RULE));

  // ---- regions strip
  let y = 108;
  pg.text('10 REGIONS', MX, y + 15, F_BOLD, 11, ink, 'l', 0.8);
  let rx = MX + 92;
  for (const r of REGIONS) {
    const n = regionCount.get(r.n) ?? 0;
    const label = r.short + ' ' + n;
    const w = F_BOLD.textWidth(label, 10, 0.3) + 12;
    pg.fillRect(rx, y + 2, w, 16, hex(r.col));
    pg.text(label, rx + 6, y + 14, F_BOLD, 10, hex('#ffffff'), 'l', 0.3);
    rx += w + 5;
  }
  // ---- fields strip (counts computed at runtime)
  y = 132;
  const fieldItems = [...fieldCount.entries()].sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]));
  pg.text('21 FIELDS', MX, y + 12, F_BOLD, 11, ink, 'l', 0.8);
  const ftext = fieldItems.map(([f, n]) => f + ' ' + n).join('  \u00b7  ');
  const flines = pg.wrap(ftext, F_SANS, 10, CW - 92);
  flines.forEach((ln, i) => pg.text(ln, MX + 92, y + 12 + i * 13, F_SANS, 10, ink));
  // ---- UTC strip
  y = 160;
  pg.fillRect(MX, y, CW, 1, hex(RULE));
  pg.text('THURSDAY IN UTC', MX, y + 14, F_BOLD, 11, ink, 'l', 0.8);
  let ux = MX + 118;
  for (const [t, label] of UTC) {
    pg.text(t, ux, y + 14, F_BOLD, 11, red, 'l');
    pg.text(label, ux + F_BOLD.textWidth(t, 11) + 6, y + 14, F_SANS, 10, ink);
    ux += F_BOLD.textWidth(t, 11) + 6 + F_SANS.textWidth(label, 10) + 16;
  }
  // ---- stats strip
  y = 182;
  pg.fillRect(MX, y, CW, 1, hex(RULE));
  const sw = CW / 5;
  STATS.forEach(([num, label], i) => {
    const cx = MX + i * sw + sw / 2;
    pg.text(num, cx, y + 20, F_SERIF, 20, red, 'c');
    pg.text(label, cx, y + 33, F_SANS, 10, soft, 'c');
    if (i) pg.fillRect(MX + i * sw, y + 4, 1, 28, hex(RULE));
  });

  // ---- heroes
  const hy = 220, hw = 312, hh = 224, hg = 16;
  HEROES.forEach((s, i) => {
    const x = MX + i * (hw + hg);
    pg.fillRect(x, hy, hw, hh, hex('#fffdf6'));
    pg.fillRect(x, hy, hw, 1, hex('#1b1712'));
    pg.fillRect(x, hy + hh - 1, hw, 1, hex(RULE));
    if (s.thumb === 'ship') sceneShip(pg, x, hy, hw, 122);
    else if (s.thumb === 'refinery') sceneRefinery(pg, x, hy, hw, 122);
    else sceneMines(pg, x, hy, hw, 122);
    numDisc(pg, x + 17, hy + 17, 22, s.no, regionCol(s.region), 12);
    kicker(pg, x, hy + 134, s);
    const hl = pg.wrap(s.head, F_SERIF, 15.5, hw - 4);
    hl.forEach((ln, k) => pg.text(ln, x, hy + 168 + k * 19, F_SERIF, 15.5, ink));
    pg.para(s.deck, x, hy + 168 + hl.length * 19 + 2, F_SANS, 11, 14, soft, hw - 4);
  });

  // ---- medium, 2 rows x 5
  const mw = (CW - 4 * 8) / 5, mh = 90;
  MEDIUM.forEach((s, i) => {
    const col = i % 5, row = Math.floor(i / 5);
    const x = MX + col * (mw + 8), yy = 452 + row * (mh + 6);
    pg.fillRect(x, yy, mw, mh, hex('#fffdf6'));
    pg.fillRect(x, yy, mw, 1, hex(RULE));
    thumb(pg, s.thumb, x, yy + 6, 54);
    numDisc(pg, x + 12, yy + 18, 18, s.no, regionCol(s.region), 11);
    const tx = x + 62, tw = mw - 66;
    pg.text(s.place, tx, yy + 12, F_BOLD, 10, ink, 'l', 0.3);
    tagChip(pg, tx, yy + 16, s.tag);
    const hl = pg.wrap(s.head, F_SERIF, 12, tw);
    hl.slice(0, 3).forEach((ln, k) => pg.text(ln, tx, yy + 44 + k * 14, F_SERIF, 12, ink));
    pg.para(s.deck, tx, yy + 44 + Math.min(3, hl.length) * 14 + 1, F_SANS, 10.5, 13, soft, tw);
  });

  // ---- bottom band: map + ALSO
  const by = 644, bh = 306;
  pg.fillRect(MX, by, CW, 1, hex('#1b1712'));
  // map panel
  const mapX = MX, mapW = 430;
  pg.text('WHERE IT HAPPENED', mapX, by + 20, F_BOLD, 14, ink, 'l', 0.8);
  pg.text('1\u201313', mapX + mapW - 4, by + 20, F_BOLD, 14, red, 'r');
  const mpx = mapX + 6, mpy = by + 28, mpw = 418, mph = 230;
  pg.fillRect(mpx, mpy, mpw, mph, hex(SEA));
  // graticule
  for (let lon = -150; lon <= 180; lon += 30) {
    const gx = mpx + ((lon + 170) / 360) * mpw;
    pg.line(gx, mpy, gx, mpy + mph, 0.7, hex('#ffffff'), 0.5);
  }
  for (let lat = -30; lat <= 60; lat += 30) {
    const gy = mpy + ((85 - lat) / 145) * mph;
    pg.line(mpx, gy, mpx + mpw, gy, 0.7, hex('#ffffff'), 0.5);
  }
  const proj = (lon: number, lat: number): [number, number] => [
    mpx + ((lon + 170) / 360) * mpw, mpy + ((85 - lat) / 145) * mph,
  ];
  for (const cont of CONTINENTS) {
    const poly = cont.map(([lo, la]) => proj(lo, la));
    pg.fillPoly([poly], hex(LAND));
    // dark coastline: draw poly edges as thin lines
    for (let i = 0; i < poly.length; i++) {
      const a = poly[i], b = poly[(i + 1) % poly.length];
      pg.line(a[0], a[1], b[0], b[1], 1, hex(LAND_D), 0.8);
    }
  }
  // dots: true positions first (leader lines), then discs
  for (const d of DOTS) {
    const [tx, ty] = proj(d.lon, d.lat);
    if (d.dx !== undefined) {
      pg.circle(tx, ty, 3, hex(regionCol(d.region)));
      pg.line(tx, ty, d.dx, d.dy, 1, hex('#5c564a'), 0.9);
    }
  }
  for (const d of DOTS) {
    const [tx, ty] = proj(d.lon, d.lat);
    const cx = d.dx ?? tx, cy = d.dy ?? ty;
    numDisc(pg, cx, cy, 18, d.no, regionCol(d.region), 11);
    if (d.label) {
      const lx = d.no === 4 ? cx - 12 - F_SANS.textWidth(d.label, 9) : cx + 12;
      pg.text(d.label, lx, cy + 3, F_SANS, 9, hex(INK));
    }
  }
  pg.text('1\u201313 numbered by story', mpx, mpy + mph + 12, F_SANS, 9, soft);
  pg.text('Equirectangular \u00b7 land in green', mpx + mpw, mpy + mph + 12, F_SANS, 9, soft, 'r');

  // ALSO list
  const ax = MX + 446, aw = CW - 446;
  pg.text('ALSO ON THURSDAY 26 NOVEMBER', ax, by + 20, F_BOLD, 14, red, 'l', 0.6);
  const colW = (aw - 12) / 2;
  const half = 19;
  for (let c = 0; c < 2; c++) {
    const items = MORE.slice(c * half, c * half + (c === 0 ? half : MORE.length - half));
    const cx0 = ax + c * (colW + 12);
    items.forEach((it, k) => {
      const iy = by + 32 + k * 14.4;
      const [no, txt, rg] = it;
      numDisc(pg, cx0 + 8, iy + 4, 15, no, regionCol(rg), 11);
      pg.text(txt, cx0 + 19, iy + 8, F_SANS, 11, ink);
    });
  }

  // ---- DATE CHECK
  const dy = 956;
  pg.fillRect(MX, dy, CW, 1, hex('#1b1712'));
  pg.fillRect(MX, dy + 2, 4, 48, red);
  pg.text('DATE CHECK', MX + 12, dy + 14, F_BOLD, 11, red, 'l', 0.8);
  pg.para('Every story above happened or was first reported on Thursday 26 November 2026.', MX + 12, dy + 28, F_SANS, 10.5, 13, ink, CW - 12);
  pg.para('Left out on purpose, first reported before Thursday: Pakistan\u2019s first astronaut docks at Tiangong; Kospi closes 6.2% down on AI doubts; Houthi strike on Riyadh tower (Tue); Ukraine\u2019s sea drones sink Russian corvette Merkury off Benghazi (Tue).', MX + 12, dy + 41, F_SANS, 10.5, 13, soft, CW - 12);
  // ---- footer
  pg.text('Sources: Reuters, AP, AFP, BBC, USGS, ESA, USTR, official statements. Every drawing original.  \u00b7  CONFIRMED = 2+ outlets \u00b7 OFFICIAL = on the record \u00b7 REPORTED = one outlet \u00b7 CLAIM = one-sided account', MX, 1021, F_SANS, 9, soft);

  grain(pg);
  const png = writePNG(pg.toRGB());
  const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, 'entry.png'), png);
}

main();
