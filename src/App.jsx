import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import {
  AlertCircle,
  AlertTriangle,
  ArrowDown,
  ArrowUp,
  ArrowUpRight,
  Check,
  Crop,
  Download,
  GripVertical,
  ImagePlus,
  Loader2,
  RotateCcw,
  RotateCw,
  ShieldCheck,
  Trash2,
  Upload,
  X,
} from 'lucide-react';
import './App.css';

/* ==========================================================================
   Constants
   ========================================================================== */

const PAGE_FORMATS = {
  a4: { label: 'A4', width: 210, height: 297 },
  letter: { label: 'Letter', width: 215.9, height: 279.4 },
  legal: { label: 'Legal', width: 215.9, height: 355.6 },
  fit: { label: 'Fit image', width: 210, height: 297 },
};

const MARGIN_MM = { none: 0, compact: 8, editorial: 18 };
const MARGIN_PHRASE = { none: 'no margins', compact: 'slim margins', editorial: 'wide margins' };

const FORMAT_OPTIONS = Object.entries(PAGE_FORMATS).map(([value, cfg]) => ({
  value,
  label: cfg.label,
}));
const ORIENTATION_OPTIONS = [
  { value: 'auto', label: 'Auto' },
  { value: 'portrait', label: 'Portrait' },
  { value: 'landscape', label: 'Landscape' },
];
const MARGIN_OPTIONS = [
  { value: 'none', label: 'None' },
  { value: 'compact', label: 'Slim' },
  { value: 'editorial', label: 'Wide' },
];
const FIT_OPTIONS = [
  { value: 'contain', label: 'Whole image' },
  { value: 'cover', label: 'Fill page' },
];

const DEFAULT_QUAD = {
  tl: { x: 0, y: 0 },
  tr: { x: 1, y: 0 },
  br: { x: 1, y: 1 },
  bl: { x: 0, y: 1 },
};

const CORNER_KEYS = ['tl', 'tr', 'br', 'bl'];
const EDGE_DEFS = [
  { key: 'top', a: 'tl', b: 'tr', label: 'Move top edge' },
  { key: 'right', a: 'tr', b: 'br', label: 'Move right edge' },
  { key: 'bottom', a: 'br', b: 'bl', label: 'Move bottom edge' },
  { key: 'left', a: 'bl', b: 'tl', label: 'Move left edge' },
];

const CROP_MODES = [
  { value: 'straighten', label: 'Straighten' },
  { value: 'cutout', label: 'Cutout' },
];

const TARGET_PRESETS_KB = [100, 200, 500, 1024];
const MIN_TARGET_KB = 25;
const MAX_TARGET_KB = 25000;
const DEFAULT_TARGET_KB = 200;
const MIN_PAGE_BUDGET = 8192;
const RESOLUTION_STEPS = [2200, 1600, 1200, 900, 680, 480, 360];

const ACCEPTED_TYPES = ['image/jpeg', 'image/jpg', 'image/png', 'image/webp'];
const ACCEPTED_EXT_RE = /\.(jpe?g|png|webp)$/i;
const JPEG_PREFIX_LENGTH = 'data:image/jpeg;base64,'.length;

const PAPER_MAX_W = 400;
const PAPER_MAX_H = 440;

/* ==========================================================================
   Small helpers & quad geometry
   ========================================================================== */

const cx = (...parts) => parts.filter(Boolean).join(' ');
const clamp = (n, lo, hi) => Math.min(hi, Math.max(lo, n));
const plural = (n, word) => `${n} ${word}${n === 1 ? '' : 's'}`;
const pause = (ms = 24) => new Promise((resolve) => setTimeout(resolve, ms));
const uid = () =>
  globalThis.crypto?.randomUUID?.() ?? `${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
const pdfOverheadBytes = (pageCount) => 4096 + pageCount * 1400;
const hasFiles = (e) => Array.from(e.dataTransfer?.types || []).includes('Files');
const isAcceptedImageFile = (file) =>
  ACCEPTED_TYPES.includes(file.type) || (!file.type && ACCEPTED_EXT_RE.test(file.name));

function cloneQuad(q = DEFAULT_QUAD) {
  return {
    tl: { x: q.tl.x, y: q.tl.y },
    tr: { x: q.tr.x, y: q.tr.y },
    br: { x: q.br.x, y: q.br.y },
    bl: { x: q.bl.x, y: q.bl.y },
  };
}

function isCroppedQuad(q) {
  if (!q) return false;
  return (
    Math.abs(q.tl.x) > 0.001 ||
    Math.abs(q.tl.y) > 0.001 ||
    Math.abs(q.tr.x - 1) > 0.001 ||
    Math.abs(q.tr.y) > 0.001 ||
    Math.abs(q.br.x - 1) > 0.001 ||
    Math.abs(q.br.y - 1) > 0.001 ||
    Math.abs(q.bl.x) > 0.001 ||
    Math.abs(q.bl.y - 1) > 0.001
  );
}

function isAxisAlignedRect(q) {
  const eps = 0.0008;
  return (
    Math.abs(q.tl.y - q.tr.y) < eps &&
    Math.abs(q.bl.y - q.br.y) < eps &&
    Math.abs(q.tl.x - q.bl.x) < eps &&
    Math.abs(q.tr.x - q.br.x) < eps
  );
}

/** Ensures the 4 corners remain a valid clockwise convex quadrilateral (no crossed edges). */
function isConvexQuad(q) {
  const pts = [q.tl, q.tr, q.br, q.bl];
  for (let i = 0; i < 4; i += 1) {
    const a = pts[i];
    const b = pts[(i + 1) % 4];
    const c = pts[(i + 2) % 4];
    const cross = (b.x - a.x) * (c.y - b.y) - (b.y - a.y) * (c.x - b.x);
    if (cross <= 0.0015) return false;
  }
  return true;
}

/** Rotates all 4 normalized crop corners 90° clockwise along with the image. */
function rotateQuadCw(q = DEFAULT_QUAD) {
  const rotPt = (p) => ({ x: clamp(1 - p.y, 0, 1), y: clamp(p.x, 0, 1) });
  return {
    tl: rotPt(q.bl),
    tr: rotPt(q.tl),
    br: rotPt(q.tr),
    bl: rotPt(q.br),
  };
}

function quadBounds(q) {
  const xs = [q.tl.x, q.tr.x, q.br.x, q.bl.x];
  const ys = [q.tl.y, q.tr.y, q.br.y, q.bl.y];
  return {
    minX: Math.min(...xs),
    maxX: Math.max(...xs),
    minY: Math.min(...ys),
    maxY: Math.max(...ys),
  };
}

function formatBytes(bytes) {
  if (!bytes || bytes <= 0) return '0 KB';
  if (bytes < 1024) return `${bytes} B`;
  const kb = bytes / 1024;
  if (kb < 1024) return `${kb.toFixed(kb >= 100 ? 0 : 1)} KB`;
  return `${(kb / 1024).toFixed(2)} MB`;
}

function loadImage(url) {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () => resolve(img);
    img.onerror = () => reject(new Error('Failed to decode image file.'));
    img.src = url;
  });
}

/* ==========================================================================
   Page layout + 4-corner perspective warp pipeline (pure functions)
   ========================================================================== */

function getEffectiveDimensions(item) {
  const isOdd = item.rotation % 180 !== 0;
  const rotW = isOdd ? item.height : item.width;
  const rotH = isOdd ? item.width : item.height;
  const q = item.crop || DEFAULT_QUAD;

  if (!isCroppedQuad(q)) {
    return { rotW, rotH, effW: rotW, effH: rotH };
  }

  if (item.cropMode === 'cutout') {
    const b = quadBounds(q);
    return {
      rotW,
      rotH,
      effW: Math.max(1, Math.round((b.maxX - b.minX) * rotW)),
      effH: Math.max(1, Math.round((b.maxY - b.minY) * rotH)),
    };
  }

  // Straightened perspective dimensions based on longest opposite edges
  const p = {
    tl: { x: q.tl.x * rotW, y: q.tl.y * rotH },
    tr: { x: q.tr.x * rotW, y: q.tr.y * rotH },
    br: { x: q.br.x * rotW, y: q.br.y * rotH },
    bl: { x: q.bl.x * rotW, y: q.bl.y * rotH },
  };
  const topW = Math.hypot(p.tr.x - p.tl.x, p.tr.y - p.tl.y);
  const botW = Math.hypot(p.br.x - p.bl.x, p.br.y - p.bl.y);
  const leftH = Math.hypot(p.bl.x - p.tl.x, p.bl.y - p.tl.y);
  const rightH = Math.hypot(p.br.x - p.tr.x, p.br.y - p.tr.y);

  return {
    rotW,
    rotH,
    effW: Math.max(1, Math.round(Math.max(topW, botW))),
    effH: Math.max(1, Math.round(Math.max(leftH, rightH))),
  };
}

function getPageDimensionsMm(effW, effH, pageFormat, orientation) {
  if (pageFormat === 'fit') {
    const pageW = 210;
    const pageH = Math.max(60, Math.min(600, pageW * (effH / effW)));
    return { pageW, pageH };
  }

  const preset = PAGE_FORMATS[pageFormat] || PAGE_FORMATS.a4;
  const landscape = orientation === 'auto' ? effW > effH : orientation === 'landscape';

  return landscape
    ? { pageW: preset.height, pageH: preset.width }
    : { pageW: preset.width, pageH: preset.height };
}

function getPageLayout(item, { pageFormat, orientation, marginStyle, fitMode }) {
  const { effW, effH } = getEffectiveDimensions(item);
  const { pageW, pageH } = getPageDimensionsMm(effW, effH, pageFormat, orientation);
  const margin = pageFormat === 'fit' ? 0 : MARGIN_MM[marginStyle];
  const availW = pageW - margin * 2;
  const availH = pageH - margin * 2;

  return {
    pageW,
    pageH,
    margin,
    availW,
    availH,
    printableRatio: availW / availH,
    activeFit: pageFormat === 'fit' ? 'contain' : fitMode,
  };
}

/** Draws the rotated source image onto an offscreen canvas capped at maxSrcDim. */
function drawRotatedSource(img, rotation, maxSrcDim) {
  const isOdd = rotation % 180 !== 0;
  const rotW = isOdd ? img.naturalHeight : img.naturalWidth;
  const rotH = isOdd ? img.naturalWidth : img.naturalHeight;
  const scale = Math.min(1, maxSrcDim / Math.max(rotW, rotH));
  const w = Math.max(1, Math.round(rotW * scale));
  const h = Math.max(1, Math.round(rotH * scale));

  const canvas = document.createElement('canvas');
  canvas.width = w;
  canvas.height = h;
  const ctx = canvas.getContext('2d');
  ctx.fillStyle = '#FFFFFF';
  ctx.fillRect(0, 0, w, h);
  ctx.imageSmoothingQuality = 'high';
  ctx.translate(w / 2, h / 2);
  ctx.rotate((rotation * Math.PI) / 180);
  const dw = isOdd ? h : w;
  const dh = isOdd ? w : h;
  ctx.drawImage(img, -dw / 2, -dh / 2, dw, dh);
  return canvas;
}

/**
 * Exact projective homography from unit square [0,1]x[0,1] to 4 source points (p0..p3)
 * with bilinear interpolation so tilted pages become crisp, straight rectangles.
 */
function warpPerspectiveCanvas(srcCanvas, quad, dstW, dstH) {
  const srcW = srcCanvas.width;
  const srcH = srcCanvas.height;
  const srcCtx = srcCanvas.getContext('2d', { willReadFrequently: true });
  const srcData = srcCtx.getImageData(0, 0, srcW, srcH).data;

  const dstCanvas = document.createElement('canvas');
  dstCanvas.width = dstW;
  dstCanvas.height = dstH;
  const dstCtx = dstCanvas.getContext('2d');
  const dstImg = dstCtx.createImageData(dstW, dstH);
  const dst = dstImg.data;

  const maxSx = srcW - 1;
  const maxSy = srcH - 1;
  const x0 = quad.tl.x * maxSx;
  const y0 = quad.tl.y * maxSy;
  const x1 = quad.tr.x * maxSx;
  const y1 = quad.tr.y * maxSy;
  const x2 = quad.br.x * maxSx;
  const y2 = quad.br.y * maxSy;
  const x3 = quad.bl.x * maxSx;
  const y3 = quad.bl.y * maxSy;

  const dx1 = x1 - x2;
  const dx2 = x3 - x2;
  const dx3 = x0 - x1 + x2 - x3;
  const dy1 = y1 - y2;
  const dy2 = y3 - y2;
  const dy3 = y0 - y1 + y2 - y3;

  const det = dx1 * dy2 - dx2 * dy1;
  let g = 0;
  let h = 0;
  if (Math.abs(det) > 1e-9) {
    g = (dx3 * dy2 - dx2 * dy3) / det;
    h = (dx1 * dy3 - dx3 * dy1) / det;
  }

  const a = x1 - x0 + g * x1;
  const b = x3 - x0 + h * x3;
  const c = x0;
  const d = y1 - y0 + g * y1;
  const e = y3 - y0 + h * y3;
  const f = y0;

  let outIdx = 0;
  for (let y = 0; y < dstH; y += 1) {
    const v = (y + 0.5) / dstH;
    const bvPlusC = b * v + c;
    const evPlusF = e * v + f;
    const hvPlus1 = h * v + 1;

    for (let x = 0; x < dstW; x += 1) {
      const u = (x + 0.5) / dstW;
      const denom = g * u + hvPlus1;
      const invDenom = denom !== 0 ? 1 / denom : 1;
      const sx = clamp((a * u + bvPlusC) * invDenom, 0, maxSx);
      const sy = clamp((d * u + evPlusF) * invDenom, 0, maxSy);

      const ix = sx | 0;
      const iy = sy | 0;
      const ix1 = ix < maxSx ? ix + 1 : maxSx;
      const iy1 = iy < maxSy ? iy + 1 : maxSy;
      const fx = sx - ix;
      const fy = sy - iy;
      const ifx = 1 - fx;
      const ify = 1 - fy;

      const w00 = ifx * ify;
      const w10 = fx * ify;
      const w01 = ifx * fy;
      const w11 = fx * fy;

      const i00 = (iy * srcW + ix) * 4;
      const i10 = (iy * srcW + ix1) * 4;
      const i01 = (iy1 * srcW + ix) * 4;
      const i11 = (iy1 * srcW + ix1) * 4;

      dst[outIdx] =
        srcData[i00] * w00 +
        srcData[i10] * w10 +
        srcData[i01] * w01 +
        srcData[i11] * w11 +
        0.5;
      dst[outIdx + 1] =
        srcData[i00 + 1] * w00 +
        srcData[i10 + 1] * w10 +
        srcData[i01 + 1] * w01 +
        srcData[i11 + 1] * w11 +
        0.5;
      dst[outIdx + 2] =
        srcData[i00 + 2] * w00 +
        srcData[i10 + 2] * w10 +
        srcData[i01 + 2] * w01 +
        srcData[i11 + 2] * w11 +
        0.5;
      dst[outIdx + 3] = 255;
      outIdx += 4;
    }
  }

  dstCtx.putImageData(dstImg, 0, 0);
  return dstCanvas;
}

/** Builds the cropped/warped master canvas once so compression loops stay fast. */
function buildCroppedCanvas({
  img,
  rotation,
  crop = DEFAULT_QUAD,
  cropMode = 'straighten',
  maxDimension,
}) {
  const isOdd = rotation % 180 !== 0;
  const rotW = isOdd ? img.naturalHeight : img.naturalWidth;
  const rotH = isOdd ? img.naturalWidth : img.naturalHeight;

  // Fast path: no crop applied
  if (!isCroppedQuad(crop)) {
    return drawRotatedSource(img, rotation, maxDimension);
  }

  // Fast path: axis-aligned rectangular crop
  if (isAxisAlignedRect(crop)) {
    const b = quadBounds(crop);
    const sx = b.minX * rotW;
    const sy = b.minY * rotH;
    const sw = Math.max(1, (b.maxX - b.minX) * rotW);
    const sh = Math.max(1, (b.maxY - b.minY) * rotH);
    const scale = Math.min(1, maxDimension / Math.max(sw, sh));
    const w = Math.max(1, Math.round(sw * scale));
    const h = Math.max(1, Math.round(sh * scale));

    const canvas = document.createElement('canvas');
    canvas.width = w;
    canvas.height = h;
    const ctx = canvas.getContext('2d');
    ctx.fillStyle = '#FFFFFF';
    ctx.fillRect(0, 0, w, h);
    ctx.imageSmoothingQuality = 'high';
    ctx.save();
    ctx.scale(scale, scale);
    ctx.translate(-sx, -sy);
    ctx.translate(rotW / 2, rotH / 2);
    ctx.rotate((rotation * Math.PI) / 180);
    ctx.drawImage(img, -img.naturalWidth / 2, -img.naturalHeight / 2);
    ctx.restore();
    return canvas;
  }

  // Keep custom 4-sided shape as a polygon cutout on white paper
  if (cropMode === 'cutout') {
    const b = quadBounds(crop);
    const sx = b.minX * rotW;
    const sy = b.minY * rotH;
    const sw = Math.max(1, (b.maxX - b.minX) * rotW);
    const sh = Math.max(1, (b.maxY - b.minY) * rotH);
    const scale = Math.min(1, maxDimension / Math.max(sw, sh));
    const w = Math.max(1, Math.round(sw * scale));
    const h = Math.max(1, Math.round(sh * scale));

    const canvas = document.createElement('canvas');
    canvas.width = w;
    canvas.height = h;
    const ctx = canvas.getContext('2d');
    ctx.fillStyle = '#FFFFFF';
    ctx.fillRect(0, 0, w, h);
    ctx.imageSmoothingQuality = 'high';

    ctx.save();
    ctx.beginPath();
    ctx.moveTo((crop.tl.x * rotW - sx) * scale, (crop.tl.y * rotH - sy) * scale);
    ctx.lineTo((crop.tr.x * rotW - sx) * scale, (crop.tr.y * rotH - sy) * scale);
    ctx.lineTo((crop.br.x * rotW - sx) * scale, (crop.br.y * rotH - sy) * scale);
    ctx.lineTo((crop.bl.x * rotW - sx) * scale, (crop.bl.y * rotH - sy) * scale);
    ctx.closePath();
    ctx.clip();

    ctx.scale(scale, scale);
    ctx.translate(-sx, -sy);
    ctx.translate(rotW / 2, rotH / 2);
    ctx.rotate((rotation * Math.PI) / 180);
    ctx.drawImage(img, -img.naturalWidth / 2, -img.naturalHeight / 2);
    ctx.restore();
    return canvas;
  }

  // Straighten mode: 4-point perspective warp into a flat rectangular page
  const p = {
    tl: { x: crop.tl.x * rotW, y: crop.tl.y * rotH },
    tr: { x: crop.tr.x * rotW, y: crop.tr.y * rotH },
    br: { x: crop.br.x * rotW, y: crop.br.y * rotH },
    bl: { x: crop.bl.x * rotW, y: crop.bl.y * rotH },
  };
  const natW = Math.max(
    1,
    Math.max(
      Math.hypot(p.tr.x - p.tl.x, p.tr.y - p.tl.y),
      Math.hypot(p.br.x - p.bl.x, p.br.y - p.bl.y)
    )
  );
  const natH = Math.max(
    1,
    Math.max(
      Math.hypot(p.bl.x - p.tl.x, p.bl.y - p.tl.y),
      Math.hypot(p.br.x - p.tr.x, p.br.y - p.tr.y)
    )
  );
  const outScale = Math.min(1, maxDimension / Math.max(natW, natH));
  const dstW = Math.max(1, Math.round(natW * outScale));
  const dstH = Math.max(1, Math.round(natH * outScale));

  const srcCap = Math.min(2400, Math.max(maxDimension * 1.4, 1400));
  const srcCanvas = drawRotatedSource(img, rotation, srcCap);
  return warpPerspectiveCanvas(srcCanvas, crop, dstW, dstH);
}

/** Downscales a master canvas to maxDimension and optionally applies page-fill cover crop. */
function fitAndResizeCanvas(masterCanvas, maxDimension, fitMode, targetAspectRatio) {
  const srcW = masterCanvas.width;
  const srcH = masterCanvas.height;

  let sx = 0;
  let sy = 0;
  let sw = srcW;
  let sh = srcH;

  if (fitMode === 'cover' && targetAspectRatio > 0) {
    const aspect = srcW / srcH;
    if (aspect > targetAspectRatio) {
      sw = Math.round(srcH * targetAspectRatio);
      sx = Math.round((srcW - sw) / 2);
    } else if (aspect < targetAspectRatio) {
      sh = Math.round(srcW / targetAspectRatio);
      sy = Math.round((srcH - sh) / 2);
    }
  }

  const scale = Math.min(1, maxDimension / Math.max(sw, sh));
  const dstW = Math.max(1, Math.round(sw * scale));
  const dstH = Math.max(1, Math.round(sh * scale));

  if (sx === 0 && sy === 0 && dstW === srcW && dstH === srcH) {
    return masterCanvas;
  }

  const canvas = document.createElement('canvas');
  canvas.width = dstW;
  canvas.height = dstH;
  const ctx = canvas.getContext('2d');
  ctx.fillStyle = '#FFFFFF';
  ctx.fillRect(0, 0, dstW, dstH);
  ctx.imageSmoothingQuality = 'high';
  ctx.drawImage(masterCanvas, sx, sy, sw, sh, 0, 0, dstW, dstH);
  return canvas;
}

function makeThumbDataUrl(img, rotation, crop, cropMode) {
  if (!isCroppedQuad(crop)) return null;
  const canvas = buildCroppedCanvas({
    img,
    rotation,
    crop,
    cropMode,
    maxDimension: 140,
  });
  return canvas.toDataURL('image/jpeg', 0.78);
}

function encodeCanvas(canvas, quality) {
  const dataUrl = canvas.toDataURL('image/jpeg', clamp(quality, 0.08, 0.98));
  return {
    dataUrl,
    width: canvas.width,
    height: canvas.height,
    byteSize: Math.max(0, Math.ceil(((dataUrl.length - JPEG_PREFIX_LENGTH) * 3) / 4)),
  };
}

/**
 * Finds the best-looking JPEG that fits the byte budget.
 * Warps/crops the source ONCE, then searches resolution + quality efficiently.
 */
function compressToBudget({ img, rotation, crop, cropMode, budgetBytes, fitMode, targetAspectRatio }) {
  const master = buildCroppedCanvas({
    img,
    rotation,
    crop,
    cropMode,
    maxDimension: RESOLUTION_STEPS[0],
  });
  let smallest = null;

  for (const maxDimension of RESOLUTION_STEPS) {
    const canvas = fitAndResizeCanvas(master, maxDimension, fitMode, targetAspectRatio);
    const minQuality = maxDimension >= 680 ? 0.5 : 0.12;
    const maxQuality = 0.94;

    const best = encodeCanvas(canvas, maxQuality);
    if (best.byteSize <= budgetBytes) return { ...best, withinBudget: true };

    let low = minQuality;
    let high = maxQuality;
    let found = null;
    for (let i = 0; i < 6; i += 1) {
      const mid = (low + high) / 2;
      const attempt = encodeCanvas(canvas, mid);
      if (attempt.byteSize <= budgetBytes) {
        found = attempt;
        low = mid;
      } else {
        high = mid;
      }
    }
    if (found) return { ...found, withinBudget: true };

    smallest = encodeCanvas(canvas, minQuality);
    if (smallest.byteSize <= budgetBytes) return { ...smallest, withinBudget: true };
  }

  return { ...smallest, withinBudget: false };
}

function renderPage({ item, layout, budgetBytes }) {
  return compressToBudget({
    img: item.img,
    rotation: item.rotation,
    crop: item.crop || DEFAULT_QUAD,
    cropMode: item.cropMode || 'straighten',
    budgetBytes,
    fitMode: layout.activeFit,
    targetAspectRatio: layout.printableRatio,
  });
}

/* ==========================================================================
   4-Corner Freeform Perspective Crop Modal
   ========================================================================== */

function CropModal({ item, onApply, onClose }) {
  const [quad, setQuad] = useState(() => cloneQuad(item.crop || DEFAULT_QUAD));
  const [cropMode, setCropMode] = useState(item.cropMode || 'straighten');
  const frameRef = useRef(null);
  const dragRef = useRef(null);

  // Render full rotated source once for crisp corner placement
  const previewUrl = useMemo(() => {
    const canvas = drawRotatedSource(item.img, item.rotation, 1400);
    return canvas.toDataURL('image/jpeg', 0.9);
  }, [item.img, item.rotation]);

  useEffect(() => {
    const onKeyDown = (e) => {
      if (e.key === 'Escape') onClose();
    };
    window.addEventListener('keydown', onKeyDown);
    return () => window.removeEventListener('keydown', onKeyDown);
  }, [onClose]);

  const startDrag = (e, target) => {
    e.preventDefault();
    e.stopPropagation();
    const rect = frameRef.current?.getBoundingClientRect();
    if (!rect || rect.width <= 0 || rect.height <= 0) return;

    try {
      e.currentTarget.setPointerCapture?.(e.pointerId);
    } catch {
      /* ignore if pointer capture is unavailable */
    }

    dragRef.current = {
      target, // 'tl' | 'tr' | 'br' | 'bl' | 'top' | 'right' | 'bottom' | 'left' | 'move'
      startX: e.clientX,
      startY: e.clientY,
      rect,
      startQuad: cloneQuad(quad),
    };
  };

  const onPointerMove = (e) => {
    const drag = dragRef.current;
    if (!drag) return;

    const dx = (e.clientX - drag.startX) / drag.rect.width;
    const dy = (e.clientY - drag.startY) / drag.rect.height;
    const s = drag.startQuad;
    const { target } = drag;

    // Move entire 4-corner frame together without changing its shape
    if (target === 'move') {
      const b = quadBounds(s);
      const cdx = clamp(dx, -b.minX, 1 - b.maxX);
      const cdy = clamp(dy, -b.minY, 1 - b.maxY);
      setQuad({
        tl: { x: s.tl.x + cdx, y: s.tl.y + cdy },
        tr: { x: s.tr.x + cdx, y: s.tr.y + cdy },
        br: { x: s.br.x + cdx, y: s.br.y + cdy },
        bl: { x: s.bl.x + cdx, y: s.bl.y + cdy },
      });
      return;
    }

    // Move a single corner independently in any direction (X and Y)
    if (CORNER_KEYS.includes(target)) {
      const nx = clamp(s[target].x + dx, 0, 1);
      const ny = clamp(s[target].y + dy, 0, 1);

      setQuad((prev) => {
        const full = { ...prev, [target]: { x: nx, y: ny } };
        if (isConvexQuad(full)) return full;

        // Slide smoothly along valid axis if dragging right against another edge
        const onlyX = { ...prev, [target]: { x: nx, y: prev[target].y } };
        if (isConvexQuad(onlyX)) return onlyX;

        const onlyY = { ...prev, [target]: { x: prev[target].x, y: ny } };
        if (isConvexQuad(onlyY)) return onlyY;

        return prev;
      });
      return;
    }

    // Move one full edge (2 connected corners together)
    const edge = EDGE_DEFS.find((ed) => ed.key === target);
    if (edge) {
      const a0 = s[edge.a];
      const b0 = s[edge.b];
      const minDx = Math.max(-a0.x, -b0.x);
      const maxDx = Math.min(1 - a0.x, 1 - b0.x);
      const minDy = Math.max(-a0.y, -b0.y);
      const maxDy = Math.min(1 - a0.y, 1 - b0.y);
      const cdx = clamp(dx, minDx, maxDx);
      const cdy = clamp(dy, minDy, maxDy);

      setQuad((prev) => {
        const full = {
          ...prev,
          [edge.a]: { x: a0.x + cdx, y: a0.y + cdy },
          [edge.b]: { x: b0.x + cdx, y: b0.y + cdy },
        };
        if (isConvexQuad(full)) return full;

        const onlyX = {
          ...prev,
          [edge.a]: { x: a0.x + cdx, y: prev[edge.a].y },
          [edge.b]: { x: b0.x + cdx, y: prev[edge.b].y },
        };
        if (isConvexQuad(onlyX)) return onlyX;

        const onlyY = {
          ...prev,
          [edge.a]: { x: prev[edge.a].x, y: a0.y + cdy },
          [edge.b]: { x: prev[edge.b].x, y: b0.y + cdy },
        };
        if (isConvexQuad(onlyY)) return onlyY;

        return prev;
      });
    }
  };

  const endDrag = () => {
    dragRef.current = null;
  };

  // Compute preview output pixel size
  const { effW, effH } = getEffectiveDimensions({
    width: item.width,
    height: item.height,
    rotation: item.rotation,
    crop: quad,
    cropMode,
  });

  // SVG coordinates on a 100x100 normalized viewBox
  const p = {
    tl: { x: quad.tl.x * 100, y: quad.tl.y * 100 },
    tr: { x: quad.tr.x * 100, y: quad.tr.y * 100 },
    br: { x: quad.br.x * 100, y: quad.br.y * 100 },
    bl: { x: quad.bl.x * 100, y: quad.bl.y * 100 },
  };
  const polyPoints = `${p.tl.x},${p.tl.y} ${p.tr.x},${p.tr.y} ${p.br.x},${p.br.y} ${p.bl.x},${p.bl.y}`;
  const maskPath = `M 0 0 H 100 V 100 H 0 Z M ${p.tl.x} ${p.tl.y} L ${p.tr.x} ${p.tr.y} L ${p.br.x} ${p.br.y} L ${p.bl.x} ${p.bl.y} Z`;

  // Perspective-interpolated 3x3 guide lines
  const lerp = (a, b, t) => ({ x: a.x + (b.x - a.x) * t, y: a.y + (b.y - a.y) * t });
  const gridLines = [1 / 3, 2 / 3].flatMap((t) => {
    const top = lerp(p.tl, p.tr, t);
    const bot = lerp(p.bl, p.br, t);
    const left = lerp(p.tl, p.bl, t);
    const right = lerp(p.tr, p.br, t);
    return [
      { key: `v-${t}`, x1: top.x, y1: top.y, x2: bot.x, y2: bot.y },
      { key: `h-${t}`, x1: left.x, y1: left.y, x2: right.x, y2: right.y },
    ];
  });

  return (
    <div
      className="crop-backdrop"
      role="dialog"
      aria-modal="true"
      aria-labelledby="crop-modal-title"
      onClick={(e) => {
        if (e.target === e.currentTarget) onClose();
      }}
    >
      <div className="crop-modal">
        <div className="crop-head">
          <div>
            <h2 id="crop-modal-title" className="crop-title">
              Freeform 4-Corner Crop
            </h2>
            <p className="crop-sub">
              Drag any corner or edge freely · Output: {effW} × {effH} px
            </p>
          </div>
          <button type="button" className="btn-tool" onClick={onClose} aria-label="Close cropper">
            <X size={17} />
          </button>
        </div>

        <div className="crop-controls">
          <div className="crop-ratios" role="group" aria-label="Crop output mode">
            {CROP_MODES.map((m) => (
              <button
                key={m.value}
                type="button"
                className={cx('crop-btn', cropMode === m.value && 'is-on')}
                aria-pressed={cropMode === m.value}
                onClick={() => setCropMode(m.value)}
              >
                {m.label}
              </button>
            ))}
          </div>

          <button
            type="button"
            className="btn btn-quiet btn-sm"
            disabled={!isCroppedQuad(quad)}
            onClick={() => setQuad(cloneQuad(DEFAULT_QUAD))}
          >
            <RotateCcw size={14} />
            Reset corners
          </button>
        </div>

        <div className="crop-canvas-stage">
          <div ref={frameRef} className="crop-frame">
            <img src={previewUrl} alt="Adjust 4 crop corners" className="crop-img" draggable={false} />

            {/* SVG mask + polygon border + perspective 3x3 guides */}
            <svg
              className="crop-svg"
              viewBox="0 0 100 100"
              preserveAspectRatio="none"
              aria-hidden="true"
            >
              <path d={maskPath} fill="rgba(0, 0, 0, 0.62)" fillRule="evenodd" />

              {gridLines.map((ln) => (
                <line
                  key={ln.key}
                  x1={ln.x1}
                  y1={ln.y1}
                  x2={ln.x2}
                  y2={ln.y2}
                  stroke="rgba(255, 255, 255, 0.4)"
                  strokeWidth="1"
                  vectorEffect="non-scaling-stroke"
                />
              ))}

              <polygon
                points={polyPoints}
                fill="transparent"
                stroke="#ffffff"
                strokeWidth="2"
                vectorEffect="non-scaling-stroke"
                className="crop-poly-move"
                onPointerDown={(e) => startDrag(e, 'move')}
                onPointerMove={onPointerMove}
                onPointerUp={endDrag}
                onPointerCancel={endDrag}
              />
            </svg>

            {/* 4 Edge Midpoint Handles */}
            {EDGE_DEFS.map((ed) => {
              const mx = ((quad[ed.a].x + quad[ed.b].x) / 2) * 100;
              const my = ((quad[ed.a].y + quad[ed.b].y) / 2) * 100;
              return (
                <button
                  key={ed.key}
                  type="button"
                  className="crop-edge-handle"
                  style={{ left: `${mx}%`, top: `${my}%` }}
                  aria-label={ed.label}
                  onPointerDown={(e) => startDrag(e, ed.key)}
                  onPointerMove={onPointerMove}
                  onPointerUp={endDrag}
                  onPointerCancel={endDrag}
                />
              );
            })}

            {/* 4 Independent Corner Handles */}
            {CORNER_KEYS.map((cornerKey) => (
              <button
                key={cornerKey}
                type="button"
                className="crop-corner-handle"
                style={{
                  left: `${quad[cornerKey].x * 100}%`,
                  top: `${quad[cornerKey].y * 100}%`,
                }}
                aria-label={`Drag ${cornerKey} corner`}
                onPointerDown={(e) => startDrag(e, cornerKey)}
                onPointerMove={onPointerMove}
                onPointerUp={endDrag}
                onPointerCancel={endDrag}
              />
            ))}
          </div>
        </div>

        <div className="crop-foot">
          <span className="crop-foot-note">
            {cropMode === 'straighten'
              ? 'Straightens the tilted page into a flat rectangle.'
              : 'Crops the page using the exact custom 4-corner shape.'}
          </span>
          <div className="crop-foot-actions">
            <button type="button" className="btn btn-quiet" onClick={onClose}>
              Cancel
            </button>
            <button
              type="button"
              className="btn btn-primary"
              onClick={() => onApply(quad, cropMode)}
            >
              <Check size={16} />
              Apply
            </button>
          </div>
        </div>
      </div>
    </div>
  );
}

/* ==========================================================================
   Presentational components
   ========================================================================== */

function Segmented({ label, options, value, onChange }) {
  const index = Math.max(0, options.findIndex((o) => o.value === value));
  return (
    <div className="field">
      <span className="field-label">{label}</span>
      <div
        className="segmented"
        role="group"
        aria-label={label}
        style={{ '--cols': options.length, '--idx': index }}
      >
        {options.map((o) => (
          <button
            key={o.value}
            type="button"
            className={cx('seg', o.value === value && 'is-on')}
            aria-pressed={o.value === value}
            onClick={() => onChange(o.value)}
          >
            {o.label}
          </button>
        ))}
      </div>
    </div>
  );
}

/** Shows how big the PDF is versus your target limit. */
function SizeGauge({ estimated, limitBytes, original, pages, isExact, withinBudget }) {
  const scaleMax = Math.max(limitBytes * 1.15, estimated * 1.08, 1);
  const fillPct = clamp((estimated / scaleMax) * 100, 0, 100);
  const limitPct = clamp((limitBytes / scaleMax) * 100, 0, 100);
  const saved =
    original > 0 && estimated > 0 ? Math.max(0, Math.round((1 - estimated / original) * 100)) : null;

  const isOver = estimated > 0 && (estimated > limitBytes || !withinBudget);

  let note = 'Add images to see the PDF size.';
  if (estimated > 0) {
    if (isOver) {
      note = `This limit can’t be reached with ${plural(pages, 'page')}. Raise the limit or remove pages.`;
    } else {
      note =
        estimated / limitBytes >= 0.85
          ? 'Quality is tuned to land just under your limit.'
          : `Fits with ${formatBytes(limitBytes - estimated)} to spare, so quality stays high.`;
    }
  }

  return (
    <div className={cx('gauge', isOver && 'is-over')}>
      <div className="gauge-head">
        <div>
          <span className="gauge-label">{isExact ? 'Final PDF size' : 'Estimated PDF size'}</span>
          <strong className="gauge-value">{estimated > 0 ? formatBytes(estimated) : '—'}</strong>
        </div>
        <span className="gauge-limit-text">
          <i className="gauge-swatch" aria-hidden="true" />
          Limit {formatBytes(limitBytes)}
        </span>
      </div>

      <div
        className="gauge-track"
        role="meter"
        aria-label="PDF size"
        aria-valuemin={0}
        aria-valuemax={Math.round(scaleMax)}
        aria-valuenow={Math.round(estimated)}
        aria-valuetext={estimated > 0 ? formatBytes(estimated) : 'No images yet'}
      >
        <div className="gauge-fill" style={{ width: `${fillPct}%` }} />
        <div className="gauge-limit" style={{ left: `${limitPct}%` }} />
      </div>

      <p className="gauge-note">{note}</p>

      <dl className="gauge-stats">
        <div>
          <dt>Original images</dt>
          <dd>{formatBytes(original)}</dd>
        </div>
        <div>
          <dt>Reduction</dt>
          <dd>{saved !== null ? `${saved}%` : '—'}</dd>
        </div>
        <div>
          <dt>Pages</dt>
          <dd>{pages}</dd>
        </div>
      </dl>
    </div>
  );
}

/* ==========================================================================
   Main component
   ========================================================================== */

export default function App() {
  // Pages
  const [images, setImages] = useState([]);
  const [selectedId, setSelectedId] = useState(null);
  const [croppingId, setCroppingId] = useState(null);
  const [isDragging, setIsDragging] = useState(false);
  const [dragIndex, setDragIndex] = useState(null);
  const [overIndex, setOverIndex] = useState(null);
  const [confirmClear, setConfirmClear] = useState(false);

  // Target size control
  const [targetKb, setTargetKb] = useState(String(DEFAULT_TARGET_KB));

  // Page layout controls
  const [pageFormat, setPageFormat] = useState('a4');
  const [orientation, setOrientation] = useState('auto');
  const [marginStyle, setMarginStyle] = useState('compact');
  const [fitMode, setFitMode] = useState('contain');
  const [fileName, setFileName] = useState('foliopress-document');

  // Proof + export state
  const [proof, setProof] = useState(null);
  const [isProofBusy, setIsProofBusy] = useState(false);
  const [exported, setExported] = useState(null);
  const [isGenerating, setIsGenerating] = useState(false);
  const [progress, setProgress] = useState({ done: 0, total: 0 });
  const [notice, setNotice] = useState(null);

  const fileInputRef = useRef(null);
  const imagesRef = useRef(images);
  imagesRef.current = images;

  /* ---------- Derived values ---------- */

  const hasImages = images.length > 0;

  const limitKb = useMemo(
    () =>
      clamp(Math.round(Number(targetKb)) || DEFAULT_TARGET_KB, MIN_TARGET_KB, MAX_TARGET_KB),
    [targetKb]
  );

  const layoutSettings = useMemo(
    () => ({ pageFormat, orientation, marginStyle, fitMode }),
    [pageFormat, orientation, marginStyle, fitMode]
  );

  const selectedImage = useMemo(
    () => images.find((item) => item.id === selectedId) || images[0] || null,
    [images, selectedId]
  );
  const selectedIndex = selectedImage ? images.findIndex((i) => i.id === selectedImage.id) : -1;
  const croppingImage = useMemo(
    () => images.find((item) => item.id === croppingId) || null,
    [images, croppingId]
  );

  const totalOriginalBytes = useMemo(
    () => images.reduce((sum, item) => sum + item.file.size, 0),
    [images]
  );

  const paper = useMemo(() => {
    if (!selectedImage) return null;
    const layout = getPageLayout(selectedImage, layoutSettings);
    const scale = Math.min(PAPER_MAX_W / layout.pageW, PAPER_MAX_H / layout.pageH);
    return {
      fit: layout.activeFit,
      hasMargin: layout.margin > 0,
      outerStyle: {
        width: `${Math.round(layout.pageW * scale)}px`,
        aspectRatio: `${layout.pageW} / ${layout.pageH}`,
      },
      innerStyle: {
        inset: `${(layout.margin / layout.pageH) * 100}% ${(layout.margin / layout.pageW) * 100}%`,
      },
    };
  }, [selectedImage, layoutSettings]);

  // Any change to pages or settings makes a previous export "stale".
  const exportSignature = useMemo(
    () =>
      JSON.stringify([
        images.map((i) => {
          const q = i.crop || DEFAULT_QUAD;
          const pts = CORNER_KEYS.map((k) => `${q[k].x.toFixed(4)},${q[k].y.toFixed(4)}`).join(';');
          return `${i.id}:${i.rotation}:${i.cropMode || 'straighten'}:${pts}`;
        }),
        limitKb,
        pageFormat,
        orientation,
        marginStyle,
        fitMode,
      ]),
    [images, limitKb, pageFormat, orientation, marginStyle, fitMode]
  );
  const isExactSize = exported?.signature === exportSignature;
  const estimatedBytes = proof ? pdfOverheadBytes(images.length) + proof.bytes * images.length : 0;
  const displayBytes = isExactSize ? exported.bytes : estimatedBytes;

  /* ---------- Effects ---------- */

  useEffect(() => {
    document.title = 'Image to PDF Converter – compress to an exact size, 100% private';
  }, []);

  useEffect(
    () => () => {
      imagesRef.current.forEach((item) => URL.revokeObjectURL(item.url));
    },
    []
  );

  // Warm up the PDF library as soon as there is something to export.
  useEffect(() => {
    if (hasImages) import('jspdf').catch(() => { });
  }, [hasImages]);

  useEffect(() => {
    if (notice?.type !== 'success') return undefined;
    const timer = setTimeout(() => setNotice(null), 9000);
    return () => clearTimeout(timer);
  }, [notice]);

  /* ---------- Adding / editing pages ---------- */

  const handleFilesAdded = useCallback(async (fileList) => {
    setNotice(null);
    const incoming = Array.from(fileList || []);
    const valid = incoming.filter(isAcceptedImageFile);

    if (valid.length === 0) {
      setNotice({
        type: 'error',
        text: 'These files aren’t supported. Add JPG, PNG or WebP images.',
      });
      return;
    }

    const loaded = [];
    for (const file of valid) {
      const url = URL.createObjectURL(file);
      try {
        const img = await loadImage(url);
        loaded.push({
          id: uid(),
          file,
          name: file.name,
          url,
          thumbUrl: null,
          img,
          width: img.naturalWidth,
          height: img.naturalHeight,
          rotation: 0,
          crop: cloneQuad(DEFAULT_QUAD),
          cropMode: 'straighten',
        });
      } catch {
        URL.revokeObjectURL(url);
      }
    }

    if (loaded.length > 0) {
      setImages((prev) => [...prev, ...loaded]);
      setSelectedId((curr) => curr || loaded[0].id);
      setConfirmClear(false);
    }

    const skipped = incoming.length - loaded.length;
    if (skipped > 0) {
      setNotice({
        type: 'warning',
        text: `${plural(skipped, 'file')} couldn’t be added. Only readable JPG, PNG and WebP images work.`,
      });
    }
  }, []);

  // Paste screenshots or copied images straight from the clipboard.
  useEffect(() => {
    const onPaste = (e) => {
      const files = Array.from(e.clipboardData?.files || []);
      if (files.length > 0) handleFilesAdded(files);
    };
    window.addEventListener('paste', onPaste);
    return () => window.removeEventListener('paste', onPaste);
  }, [handleFilesAdded]);

  const rotateImage = (id) =>
    setImages((prev) =>
      prev.map((item) => {
        if (item.id !== id) return item;
        const nextRotation = (item.rotation + 90) % 360;
        const nextCrop = isCroppedQuad(item.crop)
          ? rotateQuadCw(item.crop)
          : cloneQuad(DEFAULT_QUAD);
        return {
          ...item,
          rotation: nextRotation,
          crop: nextCrop,
          thumbUrl: makeThumbDataUrl(item.img, nextRotation, nextCrop, item.cropMode),
        };
      })
    );

  const applyCrop = (id, nextQuad, nextCropMode) => {
    setImages((prev) =>
      prev.map((item) => {
        if (item.id !== id) return item;
        return {
          ...item,
          crop: cloneQuad(nextQuad),
          cropMode: nextCropMode,
          thumbUrl: makeThumbDataUrl(item.img, item.rotation, nextQuad, nextCropMode),
        };
      })
    );
    setCroppingId(null);
  };

  const reorder = (from, to) =>
    setImages((prev) => {
      if (from === to || to < 0 || to >= prev.length) return prev;
      const copy = [...prev];
      const [moved] = copy.splice(from, 1);
      copy.splice(to, 0, moved);
      return copy;
    });

  const removeImage = (id) => {
    const index = images.findIndex((item) => item.id === id);
    if (index === -1) return;
    URL.revokeObjectURL(images[index].url);
    const remaining = images.filter((item) => item.id !== id);
    setImages(remaining);
    if (croppingId === id) setCroppingId(null);
    if (remaining.length === 0) {
      setSelectedId(null);
      setExported(null);
      setConfirmClear(false);
    } else if (selectedImage?.id === id) {
      setSelectedId((remaining[index] || remaining[index - 1] || null)?.id ?? null);
    }
  };

  const clearAllImages = () => {
    images.forEach((item) => URL.revokeObjectURL(item.url));
    setImages([]);
    setSelectedId(null);
    setCroppingId(null);
    setProof(null);
    setExported(null);
    setConfirmClear(false);
    setNotice(null);
  };

  /* ---------- Live proof ---------- */

  useEffect(() => {
    if (!selectedImage) {
      setProof(null);
      setIsProofBusy(false);
      return undefined;
    }

    let cancelled = false;
    setIsProofBusy(true);

    const timer = setTimeout(() => {
      try {
        const layout = getPageLayout(selectedImage, layoutSettings);
        const pageCount = Math.max(1, images.length);
        const budgetBytes = Math.max(
          MIN_PAGE_BUDGET,
          Math.floor((limitKb * 1024 - pdfOverheadBytes(pageCount)) / pageCount)
        );
        const rendered = renderPage({
          item: selectedImage,
          layout,
          budgetBytes,
        });
        if (!cancelled) {
          setProof({
            url: rendered.dataUrl,
            bytes: rendered.byteSize,
            withinBudget: rendered.withinBudget,
          });
        }
      } catch {
        /* ignore transient render errors */
      } finally {
        if (!cancelled) setIsProofBusy(false);
      }
    }, 180);

    return () => {
      cancelled = true;
      clearTimeout(timer);
    };
  }, [selectedImage, images.length, limitKb, layoutSettings]);

  /* ---------- Export ---------- */

  const handleExportPdf = async () => {
    if (images.length === 0 || isGenerating) return;

    const total = images.length;
    setIsGenerating(true);
    setNotice(null);
    setProgress({ done: 0, total });

    try {
      const { jsPDF } = await import('jspdf');

      const safeName = (fileName.trim() || 'foliopress-document')
        .replace(/\.pdf$/i, '')
        .replace(/[\\/:*?"<>|]+/g, '-');
      const finalName = `${safeName}.pdf`;

      // Whatever one page doesn't use is handed to the pages after it.
      const totalBudget = Math.max(0, limitKb * 1024 - pdfOverheadBytes(total));
      let spent = 0;
      let doc = null;

      for (let i = 0; i < total; i += 1) {
        setProgress({ done: i, total });
        await pause();

        const item = images[i];
        const layout = getPageLayout(item, layoutSettings);
        const budgetBytes = Math.max(
          MIN_PAGE_BUDGET,
          Math.floor((totalBudget - spent) / (total - i))
        );

        const rendered = renderPage({
          item,
          layout,
          budgetBytes,
        });
        spent += rendered.byteSize;

        const pdfOrient = layout.pageW > layout.pageH ? 'l' : 'p';
        if (i === 0) {
          doc = new jsPDF({
            orientation: pdfOrient,
            unit: 'mm',
            format: [layout.pageW, layout.pageH],
            compress: true,
          });
          doc.setProperties({ title: safeName, creator: 'FolioPress' });
        } else {
          doc.addPage([layout.pageW, layout.pageH], pdfOrient);
        }

        let drawW = layout.availW;
        let drawH = layout.availH;
        let x = layout.margin;
        let y = layout.margin;

        if (layout.activeFit === 'contain') {
          const imgRatio = rendered.width / rendered.height;
          if (imgRatio > layout.printableRatio) {
            drawH = layout.availW / imgRatio;
            y = layout.margin + (layout.availH - drawH) / 2;
          } else {
            drawW = layout.availH * imgRatio;
            x = layout.margin + (layout.availW - drawW) / 2;
          }
        }

        doc.addImage(rendered.dataUrl, 'JPEG', x, y, drawW, drawH, undefined, 'FAST');
      }

      setProgress({ done: total, total });
      const pdfBlob = doc.output('blob');
      const downloadUrl = URL.createObjectURL(pdfBlob);
      const link = document.createElement('a');
      link.href = downloadUrl;
      link.download = finalName;
      document.body.appendChild(link);
      link.click();
      document.body.removeChild(link);
      setTimeout(() => URL.revokeObjectURL(downloadUrl), 5000);

      setExported({ bytes: pdfBlob.size, signature: exportSignature });

      const overLimit = pdfBlob.size > limitKb * 1024;
      setNotice(
        overLimit
          ? {
            type: 'warning',
            text: `Downloaded ${finalName} at ${formatBytes(pdfBlob.size)}, over your ${formatBytes(
              limitKb * 1024
            )} limit. Raise the limit or remove pages.`,
          }
          : {
            type: 'success',
            text: `Downloaded ${finalName}: ${formatBytes(pdfBlob.size)}, ${plural(total, 'page')}.`,
          }
      );
    } catch (err) {
      setNotice({
        type: 'error',
        text: err?.message || 'Could not build the PDF. Re-add your images and try again.',
      });
    } finally {
      setIsGenerating(false);
    }
  };

  /* ---------- Drag & drop (files from the desktop) ---------- */

  const onStageDragOver = (e) => {
    if (!hasFiles(e)) return;
    e.preventDefault();
    setIsDragging(true);
  };
  const onStageDragLeave = (e) => {
    if (!e.currentTarget.contains(e.relatedTarget)) setIsDragging(false);
  };
  const onStageDrop = (e) => {
    if (!hasFiles(e)) return;
    e.preventDefault();
    setIsDragging(false);
    handleFilesAdded(e.dataTransfer.files);
  };

  const resetRowDrag = () => {
    setDragIndex(null);
    setOverIndex(null);
  };

  const progressPct = progress.total ? (progress.done / progress.total) * 100 : 0;
  const NoticeIcon =
    notice?.type === 'error' ? AlertCircle : notice?.type === 'warning' ? AlertTriangle : Check;
  const selectedIsCropped = selectedImage ? isCroppedQuad(selectedImage.crop) : false;

  /* ---------- Render ---------- */

  return (
    <div className="app">
      <main
        className="workspace"
        onDragOver={onStageDragOver}
        onDragLeave={onStageDragLeave}
        onDrop={onStageDrop}
      >
        <div className="container">
          <div className="intro">
            <h1>Image to PDF Converter</h1>
            <p>
              Turn JPG, PNG and WebP images into one PDF and fit it under an exact size such as 100
              KB or 200 KB. Perspective-crop, reorder, rotate and preview every page before you
              download.
            </p>
            <p className="trust-line">
              <ShieldCheck size={17} />
              100% private. Your images are processed on your device and never uploaded.
            </p>
          </div>

          <input
            ref={fileInputRef}
            type="file"
            accept=".jpg,.jpeg,.png,.webp,image/jpeg,image/png,image/webp"
            multiple
            className="hidden-input"
            onChange={(e) => {
              handleFilesAdded(e.target.files);
              e.target.value = '';
            }}
          />

          <div className={cx('studio', !hasImages && 'studio--empty')}>
            {isDragging && hasImages && <div className="drop-veil">Drop to add more pages</div>}

            {!hasImages ? (
              <div
                className={cx('dropzone', isDragging && 'is-over')}
                role="button"
                tabIndex={0}
                onClick={() => fileInputRef.current?.click()}
                onKeyDown={(e) => {
                  if (e.key === 'Enter' || e.key === ' ') {
                    e.preventDefault();
                    fileInputRef.current?.click();
                  }
                }}
              >
                <div className="dz-stack" aria-hidden="true">
                  <span className="dz-sheet" />
                  <span className="dz-sheet" />
                  <span className="dz-sheet">
                    <Upload size={28} />
                  </span>
                </div>
                <h2>Drop your images here</h2>
                <p>
                  JPG, PNG or WebP. You can also paste a screenshot with Ctrl+V, then crop any
                  corner freely, reorder and rotate pages before exporting.
                </p>
                <span className="btn btn-primary">Choose images</span>
              </div>
            ) : (
              <>
                {/* Pages */}
                <section className="panel pages-panel" aria-label="Pages">
                  <div className="panel-head">
                    <h2 className="panel-title">
                      Pages <span className="count-chip">{images.length}</span>
                    </h2>
                    <button
                      type="button"
                      className="btn btn-soft btn-sm"
                      onClick={() => fileInputRef.current?.click()}
                    >
                      <ImagePlus size={15} />
                      Add
                    </button>
                  </div>

                  <ul className="page-list">
                    {images.map((item, idx) => {
                      const active = selectedImage?.id === item.id;
                      const cropped = isCroppedQuad(item.crop);
                      const { effW, effH } = getEffectiveDimensions(item);
                      return (
                        <li
                          key={item.id}
                          className={cx(
                            'page-row',
                            active && 'is-active',
                            dragIndex === idx && 'is-dragging',
                            overIndex === idx &&
                            dragIndex !== null &&
                            dragIndex !== idx &&
                            'is-drop-target'
                          )}
                          draggable
                          onDragStart={(e) => {
                            setDragIndex(idx);
                            e.dataTransfer.effectAllowed = 'move';
                            e.dataTransfer.setData('text/plain', item.id);
                          }}
                          onDragOver={(e) => {
                            if (dragIndex === null) return;
                            e.preventDefault();
                            e.stopPropagation();
                            setOverIndex(idx);
                          }}
                          onDrop={(e) => {
                            if (dragIndex === null) return;
                            e.preventDefault();
                            e.stopPropagation();
                            reorder(dragIndex, idx);
                            resetRowDrag();
                          }}
                          onDragEnd={resetRowDrag}
                        >
                          <div
                            className="page-select"
                            role="button"
                            tabIndex={0}
                            aria-current={active ? 'true' : undefined}
                            onClick={() => setSelectedId(item.id)}
                            onKeyDown={(e) => {
                              if (e.key === 'Enter' || e.key === ' ') {
                                e.preventDefault();
                                setSelectedId(item.id);
                              }
                            }}
                          >
                            <span className="page-grip" aria-hidden="true">
                              <GripVertical size={16} />
                            </span>
                            <span className="page-thumb">
                              <img
                                src={item.thumbUrl || item.url}
                                alt=""
                                loading="lazy"
                                style={
                                  item.thumbUrl
                                    ? undefined
                                    : { transform: `rotate(${item.rotation}deg)` }
                                }
                              />
                            </span>
                            <span className="page-text">
                              <span className="page-name" title={item.name}>
                                {item.name}
                              </span>
                              <span className="page-meta">
                                {effW} × {effH} px, {formatBytes(item.file.size)}
                                {item.rotation > 0 ? `, rotated ${item.rotation}°` : ''}
                                {cropped ? ', cropped' : ''}
                              </span>
                            </span>
                            <span className="page-index">{idx + 1}</span>
                          </div>
                        </li>
                      );
                    })}
                  </ul>

                  <div className="panel-foot">
                    <span className="foot-total">Total {formatBytes(totalOriginalBytes)}</span>
                    {confirmClear ? (
                      <div className="confirm" role="group" aria-label="Confirm clearing all pages">
                        <span>Remove all?</span>
                        <button
                          type="button"
                          className="btn btn-primary btn-sm"
                          onClick={clearAllImages}
                        >
                          Remove
                        </button>
                        <button
                          type="button"
                          className="btn btn-quiet btn-sm"
                          onClick={() => setConfirmClear(false)}
                        >
                          Keep
                        </button>
                      </div>
                    ) : (
                      <button
                        type="button"
                        className="btn btn-quiet btn-sm"
                        onClick={() => setConfirmClear(true)}
                      >
                        Clear all
                      </button>
                    )}
                  </div>
                </section>

                {/* Stage: proof + size gauge */}
                <section className="stage" aria-label="Page preview">
                  <div className="stage-toolbar">
                    <div className="stage-title">
                      <strong>
                        Page {selectedIndex + 1} of {images.length}
                      </strong>
                      <span className="stage-sub">
                        {PAGE_FORMATS[pageFormat].label},{' '}
                        {pageFormat === 'fit' ? 'no margins' : MARGIN_PHRASE[marginStyle]}
                      </span>
                    </div>

                    <div className="toolbar-actions">
                      <button
                        type="button"
                        className={cx('btn-tool', selectedIsCropped && 'btn-tool--active')}
                        onClick={() => setCroppingId(selectedImage.id)}
                        title="4-Corner freeform crop"
                      >
                        <Crop size={16} />
                        <span className="tool-label">
                          {selectedIsCropped ? 'Cropped' : 'Crop'}
                        </span>
                      </button>
                      <button
                        type="button"
                        className="btn-tool"
                        onClick={() => rotateImage(selectedImage.id)}
                        title="Rotate 90°"
                      >
                        <RotateCw size={16} />
                        <span className="tool-label">Rotate</span>
                      </button>
                      <button
                        type="button"
                        className="btn-tool"
                        disabled={selectedIndex <= 0}
                        onClick={() => reorder(selectedIndex, selectedIndex - 1)}
                        title="Move page up"
                        aria-label="Move page up"
                      >
                        <ArrowUp size={16} />
                      </button>
                      <button
                        type="button"
                        className="btn-tool"
                        disabled={selectedIndex >= images.length - 1}
                        onClick={() => reorder(selectedIndex, selectedIndex + 1)}
                        title="Move page down"
                        aria-label="Move page down"
                      >
                        <ArrowDown size={16} />
                      </button>
                      <button
                        type="button"
                        className="btn-tool btn-tool--danger"
                        onClick={() => removeImage(selectedImage.id)}
                        title="Remove page"
                      >
                        <Trash2 size={16} />
                        <span className="tool-label">Remove</span>
                      </button>
                    </div>
                  </div>

                  <div className="desk">
                    {paper && (
                      <div className="paper" style={paper.outerStyle}>
                        <div
                          className={cx('paper-content', paper.hasMargin && 'has-margin')}
                          style={paper.innerStyle}
                        >
                          {proof && (
                            <img
                              src={proof.url}
                              alt="Compressed preview of the selected page"
                              style={{ objectFit: paper.fit }}
                            />
                          )}
                        </div>
                      </div>
                    )}
                    {isProofBusy && (
                      <span className="paper-busy" role="status">
                        <Loader2 size={14} className="spin" />
                        Updating preview
                      </span>
                    )}
                  </div>

                  <SizeGauge
                    estimated={displayBytes}
                    limitBytes={limitKb * 1024}
                    original={totalOriginalBytes}
                    pages={images.length}
                    isExact={isExactSize}
                    withinBudget={proof ? proof.withinBudget : true}
                  />
                </section>
              </>
            )}

            {/* Settings */}
            <aside className="panel settings" aria-label="Export settings">
              <div className="settings-body">
                <section className="group">

                  <div className="field">
                    <div className="field-row">
                      <label className="field-label" htmlFor="target-kb-input">
                        Maximum PDF size
                      </label>
                    </div>
                    <div className="chips">
                      {TARGET_PRESETS_KB.map((kb) => (
                        <button
                          key={kb}
                          type="button"
                          className={cx('chip', limitKb === kb && 'is-on')}
                          aria-pressed={limitKb === kb}
                          onClick={() => setTargetKb(String(kb))}
                        >
                          {kb >= 1024 ? '1 MB' : `${kb} KB`}
                        </button>
                      ))}
                    </div>
                    <div className="input-row">
                      <input
                        id="target-kb-input"
                        type="number"
                        inputMode="numeric"
                        min={MIN_TARGET_KB}
                        max={MAX_TARGET_KB}
                        step={10}
                        className="input"
                        value={targetKb}
                        onChange={(e) => setTargetKb(e.target.value)}
                        onBlur={() => setTargetKb(String(limitKb))}
                      />
                      <span className="input-unit">KB</span>
                    </div>
                    <p className="hint">
                      Quality and resolution are tuned page by page so the whole PDF stays under
                      this size.
                    </p>
                  </div>
                </section>

                <section className="group">

                  <Segmented
                    label="Format"
                    options={FORMAT_OPTIONS}
                    value={pageFormat}
                    onChange={setPageFormat}
                  />

                  {pageFormat === 'fit' ? (
                    <p className="hint">
                      Each page takes the shape of its image, so orientation, margins and fit don’t
                      apply.
                    </p>
                  ) : (
                    <>
                      <Segmented
                        label="Orientation"
                        options={ORIENTATION_OPTIONS}
                        value={orientation}
                        onChange={setOrientation}
                      />
                      <Segmented
                        label="Margins"
                        options={MARGIN_OPTIONS}
                        value={marginStyle}
                        onChange={setMarginStyle}
                      />
                      <Segmented
                        label="Image fit"
                        options={FIT_OPTIONS}
                        value={fitMode}
                        onChange={setFitMode}
                      />
                    </>
                  )}
                </section>

                <section className="group">

                  <div className="field">
                    <label className="field-label" htmlFor="pdf-filename">
                      File name
                    </label>
                    <div className="input-row">
                      <input
                        id="pdf-filename"
                        type="text"
                        className="input"
                        value={fileName}
                        onChange={(e) => setFileName(e.target.value)}
                        placeholder="foliopress-document"
                      />
                      <span className="input-unit">.pdf</span>
                    </div>
                  </div>
                </section>
              </div>

              <div className="settings-foot">
                <button
                  type="button"
                  className="btn btn-primary btn-export"
                  disabled={!hasImages || isGenerating}
                  onClick={handleExportPdf}
                >
                  {isGenerating ? (
                    <>
                      <Loader2 size={18} className="spin" />
                      Building page {Math.min(progress.done + 1, progress.total)} of {progress.total}
                    </>
                  ) : (
                    <>
                      <Download size={18} />
                      Download PDF{hasImages ? ` (${plural(images.length, 'page')})` : ''}
                    </>
                  )}
                </button>

                {isGenerating && (
                  <div
                    className="progress"
                    role="progressbar"
                    aria-label="Building PDF"
                    aria-valuemin={0}
                    aria-valuemax={progress.total}
                    aria-valuenow={progress.done}
                  >
                    <span style={{ width: `${progressPct}%` }} />
                  </div>
                )}

                {notice && (
                  <div
                    className={cx('notice', `notice--${notice.type}`)}
                    role={notice.type === 'error' ? 'alert' : 'status'}
                  >
                    <NoticeIcon size={17} className="notice-icon" />
                    <span>{notice.text}</span>
                    <button
                      type="button"
                      className="notice-close"
                      aria-label="Dismiss message"
                      onClick={() => setNotice(null)}
                    >
                      <X size={15} />
                    </button>
                  </div>
                )}
              </div>
            </aside>
          </div>
        </div>
      </main>

      {croppingImage && (
        <CropModal
          item={croppingImage}
          onApply={(nextQuad, nextCropMode) => applyCrop(croppingImage.id, nextQuad, nextCropMode)}
          onClose={() => setCroppingId(null)}
        />
      )}

      <aside className="project-callout" aria-label="More projects">
        <span className="project-callout-text">
          Only need to shrink image size without making a PDF? Check out my other project:
        </span>
        <a
          href="https://image-compresser-nu.vercel.app/"
          target="_blank"
          rel="noopener noreferrer"
          className="project-callout-link"
        >
          <span>Image Compressor</span>
          <ArrowUpRight size={15} className="project-callout-icon" aria-hidden="true" />
        </a>
      </aside>
    </div>
  );
}