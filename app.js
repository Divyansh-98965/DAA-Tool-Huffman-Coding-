/**
 * Huffman Coding Visualizer — Anti-Gravity Edition
 * Step-by-Step Tree Construction, Min-Heap Animation, Compression & Decoding
 */

(function () {
  'use strict';

  /* ─── Google Primary Colors ─── */
  const COLORS = ['#4285F4', '#EA4335', '#FBBC05', '#34A853'];
  const BLUE = COLORS[0], RED = COLORS[1], YELLOW = COLORS[2], GREEN = COLORS[3];

  /* ─── Visual Constants ─── */
  const NODE_RADIUS = 21;

  /* ─── App State ─── */
  let huffmanRoot = null;
  let codes = {};
  let freqMap = new Map();
  let inputText = '';
  let overheadMode = 'standard'; // 'standard' (includes tree overhead) | 'canonical' (zero tree overhead)

  // Step-by-step construction state
  let buildSteps = [];
  let currentStep = 0;
  let stepProgress = 1.0;
  let isPlaying = false;
  let isAnimating = false;
  let playDelayTimeout = null;
  let speedMultiplier = 1;
  let nodeMap = new Map();       // id -> HNode
  let treeNodes = [];            // flat list of laid out nodes

  // Canvas pan & zoom
  let panOffset = { x: 0, y: 0 };
  let zoomLevel = 1;
  let isPanning = false;
  let panStart = { x: 0, y: 0 };

  // Decode state
  let decodeTimer = null;
  let isDecoding = false;
  let decodeIndex = 0;
  let decodedText = '';
  let decodeCurrentNode = null;
  let decodeHighlightPath = [];
  let decodeSpeed = 1;

  /* ═══════════════════════════════════════════════════════════
     BACKGROUND WALLPAPER SYSTEM
     Replaced animated particle canvas with static wallpapers:
     - Light_mode.jpg for light mode
     - Dark_mode.jpg for dark mode
     ═══════════════════════════════════════════════════════════ */
  // Particle system replaced with responsive wallpaper backgrounds in CSS

  /* ═══════════════════════════════════════════════════════════
     HUFFMAN ENGINE & STEP GENERATION
     ═══════════════════════════════════════════════════════════ */

  function buildFrequencyMap(text) {
    const freq = new Map();
    for (const ch of text) {
      freq.set(ch, (freq.get(ch) || 0) + 1);
    }
    return freq;
  }

  class HNode {
    constructor(char, freq, left = null, right = null) {
      this.char = char;
      this.freq = freq;
      this.left = left;
      this.right = right;
      this.id = HNode._id++;
      this.x = 0;
      this.y = 0;
      this.targetX = 0;
      this.targetY = 0;
    }
  }
  HNode._id = 0;

  function cloneQueueNode(n) {
    if (!n) return null;
    return {
      id: n.id,
      char: n.char,
      freq: n.freq,
      isLeaf: !n.left && !n.right,
    };
  }

  function displayChar(ch) {
    if (ch === null || ch === undefined) return '';
    if (ch === ' ') return '␣';
    if (ch === '\n') return '↵';
    if (ch === '\t') return '⇥';
    return ch;
  }

  function easeInOutCubic(x) {
    return x < 0.5 ? 4 * x * x * x : 1 - Math.pow(-2 * x + 2, 3) / 2;
  }

  /**
   * Builds the Huffman Tree and records granular step-by-step actions:
   * 1. Step 0: Initial Min-Heap queue
   * 2. Step 1..M: Extract 2 smallest, lift & merge into parent, insert parent back into sorted queue
   * 3. Final Step: Single root node remains in queue, tree complete
   */
  function buildHuffmanTree(freq) {
    buildSteps = [];
    HNode._id = 0;

    if (freq.size === 0) return null;

    // Collect initial leaf nodes
    const leaves = [];
    for (const [char, f] of freq) {
      leaves.push(new HNode(char, f));
    }
    // Stable sort ascending by frequency, tie-break by character
    leaves.sort((a, b) => a.freq - b.freq || a.char.localeCompare(b.char));

    let queue = [...leaves];

    // Step 0: Initial Priority Queue state
    buildSteps.push({
      type: 'init',
      stepNumber: 0,
      badge: 'Step 0: Initial Queue',
      description: `Min-Heap initialized with ${leaves.length} character nodes sorted by frequency. Click Play or Step Forward to begin merging.`,
      queueBefore: queue.map(cloneQueueNode),
      queueAfter: queue.map(cloneQueueNode),
      min1: null,
      min2: null,
      parent: null,
      activeEdges: [],
      activeNodes: [],
    });

    // Special edge case: single unique character
    if (leaves.length === 1) {
      const only = leaves[0];
      const root = new HNode(null, only.freq, only, null);
      buildSteps.push({
        type: 'merge',
        stepNumber: 1,
        mergeIndex: 1,
        badge: 'Step 1: Root Node',
        description: `Step 1: Single unique character '${displayChar(only.char)}' (${only.freq}) wrapped into root node (${root.freq}).`,
        queueBefore: [cloneQueueNode(only)],
        queueAfter: [cloneQueueNode(root)],
        insertIdx: 0,
        min1: cloneQueueNode(only),
        min2: null,
        parent: cloneQueueNode(root),
        newEdges: [{ from: root.id, to: only.id, bit: '0' }],
        activeEdges: [{ from: root.id, to: only.id, bit: '0' }],
        activeNodes: [root.id, only.id],
      });
      buildSteps.push({
        type: 'complete',
        stepNumber: 2,
        badge: 'Complete',
        description: `Huffman Tree construction complete! Root node (${root.freq}) represents the entire optimal prefix code tree.`,
        queueBefore: [cloneQueueNode(root)],
        queueAfter: [cloneQueueNode(root)],
        min1: null,
        min2: null,
        parent: null,
        activeEdges: [{ from: root.id, to: only.id, bit: '0' }],
        activeNodes: [root.id, only.id],
      });
      return root;
    }

    let mergeIdx = 1;
    const accumulatedEdges = [];
    const accumulatedNodes = new Set();

    while (queue.length > 1) {
      // 1. Pick the two lowest-frequency nodes
      const left = queue[0];
      const right = queue[1];
      const queueBefore = queue.map(cloneQueueNode);

      // 2. Remove the two lowest nodes from queue
      queue.splice(0, 2);

      // 3. Create new parent node with combined sum frequency
      const parent = new HNode(null, left.freq + right.freq, left, right);

      // 4. Insert new parent back into queue in sorted position (after equal frequencies)
      let insertIdx = queue.findIndex(n => n.freq > parent.freq);
      if (insertIdx === -1) {
        queue.push(parent);
        insertIdx = queue.length - 1;
      } else {
        queue.splice(insertIdx, 0, parent);
      }

      accumulatedEdges.push({ from: parent.id, to: left.id, bit: '0' });
      accumulatedEdges.push({ from: parent.id, to: right.id, bit: '1' });
      accumulatedNodes.add(parent.id);
      accumulatedNodes.add(left.id);
      accumulatedNodes.add(right.id);

      const queueAfter = queue.map(cloneQueueNode);

      const leftLabel = left.char !== null ? `'${displayChar(left.char)}'` : `parent node (${left.freq})`;
      const rightLabel = right.char !== null ? `'${displayChar(right.char)}'` : `parent node (${right.freq})`;

      buildSteps.push({
        type: 'merge',
        stepNumber: mergeIdx,
        mergeIndex: mergeIdx,
        badge: `Step ${mergeIdx}`,
        description: `Step ${mergeIdx}: Selecting lowest frequency nodes ${leftLabel} (${left.freq}) and ${rightLabel} (${right.freq}) to merge into parent node (${parent.freq}).`,
        queueBefore: queueBefore,
        queueAfter: queueAfter,
        insertIdx: insertIdx,
        min1: cloneQueueNode(left),
        min2: cloneQueueNode(right),
        parent: cloneQueueNode(parent),
        newEdges: [
          { from: parent.id, to: left.id, bit: '0' },
          { from: parent.id, to: right.id, bit: '1' },
        ],
        activeEdges: [...accumulatedEdges],
        activeNodes: Array.from(accumulatedNodes),
      });

      mergeIdx++;
    }

    const finalRoot = queue[0];
    buildSteps.push({
      type: 'complete',
      stepNumber: mergeIdx,
      badge: 'Complete',
      description: `Huffman Tree construction complete! Only the root node (${finalRoot.freq}) remains in the queue.`,
      queueBefore: [cloneQueueNode(finalRoot)],
      queueAfter: [cloneQueueNode(finalRoot)],
      min1: null,
      min2: null,
      parent: null,
      activeEdges: [...accumulatedEdges],
      activeNodes: Array.from(accumulatedNodes),
    });

    return finalRoot;
  }

  function assignCodes(node, prefix = '', result = {}) {
    if (!node) return result;
    if (!node.left && !node.right) {
      result[node.char] = prefix || '0';
      return result;
    }
    assignCodes(node.left, prefix + '0', result);
    assignCodes(node.right, prefix + '1', result);
    return result;
  }

  function encodeText(text, codes) {
    return [...text].map(ch => codes[ch]).join('');
  }

  /* ═══════════════════════════════════════════════════════════
     TREE LAYOUT ALGORITHM
     ═══════════════════════════════════════════════════════════ */

  function layoutTree(root, canvasWidth, canvasHeight) {
    nodeMap = new Map();
    if (!root) return [];

    function getDepth(n) {
      return n ? 1 + Math.max(getDepth(n.left), getDepth(n.right)) : 0;
    }

    const treeDepth = getDepth(root);
    // Reserve bottom 130px for the priority queue shelf
    const usableHeight = Math.max(160, canvasHeight - 160);
    const levelHeight = Math.min(68, usableHeight / Math.max(treeDepth, 1));
    const baseSpread = Math.min(canvasWidth * 0.42, 330);

    const list = [];
    function layout(node, cx, cy, spread, d) {
      if (!node) return;
      node.targetX = cx;
      node.targetY = cy;
      node.x = cx;
      node.y = cy;
      node._depth = d;
      nodeMap.set(node.id, node);
      list.push(node);
      const childSpread = spread * 0.52;
      layout(node.left, cx - spread, cy + levelHeight, childSpread, d + 1);
      layout(node.right, cx + spread, cy + levelHeight, childSpread, d + 1);
    }

    layout(root, canvasWidth / 2, 45, baseSpread, 0);
    return list;
  }

  /* ═══════════════════════════════════════════════════════════
     CANVAS STEP RENDERING (Ground Up Step-by-Step Animation)
     ═══════════════════════════════════════════════════════════ */

  function drawRoundRect(ctx, x, y, w, h, r) {
    if (w < 2 * r) r = w / 2;
    if (h < 2 * r) r = h / 2;
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  function drawBadge(ctx, x, y, text, bgColor, textColor = '#FFFFFF') {
    ctx.font = 'bold 9px "Roboto Mono", monospace';
    const textW = ctx.measureText(text).width;
    const padX = 6;
    const badgeW = textW + padX * 2;
    const badgeH = 16;
    const badgeX = x - badgeW / 2;
    const badgeY = y - badgeH / 2;

    ctx.save();
    drawRoundRect(ctx, badgeX, badgeY, badgeW, badgeH, 8);
    ctx.fillStyle = bgColor;
    ctx.fill();

    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillStyle = textColor;
    ctx.fillText(text, x, y);
    ctx.restore();
  }

  function drawEdgeWithLabel(ctx, x1, y1, x2, y2, bit, progress, isDark) {
    const curX = x1 + (x2 - x1) * progress;
    const curY = y1 + (y2 - y1) * progress;
    const edgeColor = (bit === '0') ? BLUE : RED;

    // Draw branch line
    ctx.beginPath();
    ctx.moveTo(x1, y1);
    ctx.lineTo(curX, curY);
    ctx.strokeStyle = edgeColor;
    ctx.lineWidth = 2.5;
    ctx.lineCap = 'round';
    ctx.stroke();

    // Draw animated branch bit label at midpoint when progress >= 0.4
    if (progress >= 0.4) {
      const alpha = Math.min(1, (progress - 0.4) / 0.5);
      const mx = (x1 + x2) / 2;
      const my = (y1 + y2) / 2;

      ctx.save();
      ctx.globalAlpha = alpha;
      drawBadge(ctx, mx, my, bit, edgeColor, '#FFFFFF');
      ctx.restore();
    }
  }

  function drawQueueNode(ctx, x, y, item, opts) {
    const { isJustInserted, isRootDone, isDark, textColor, bgSurface } = opts;
    const r = 18;

    ctx.save();
    ctx.beginPath();
    ctx.arc(x, y, r, 0, Math.PI * 2);

    if (isJustInserted) {
      ctx.fillStyle = isDark ? '#143825' : '#E6F4EA';
      ctx.shadowColor = GREEN;
      ctx.shadowBlur = 14;
    } else if (isRootDone) {
      ctx.fillStyle = isDark ? '#3D3008' : '#FEF7E0';
      ctx.shadowColor = YELLOW;
      ctx.shadowBlur = 14;
    } else {
      ctx.fillStyle = bgSurface;
      ctx.shadowColor = 'transparent';
      ctx.shadowBlur = 0;
    }
    ctx.fill();

    ctx.shadowBlur = 0;
    ctx.strokeStyle = item.isLeaf ? GREEN : (isJustInserted ? GREEN : (isDark ? '#4285F4' : '#1A73E8'));
    ctx.lineWidth = item.isLeaf ? 2.2 : 2.0;
    ctx.stroke();

    // Text
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    if (item.isLeaf) {
      ctx.font = 'bold 12px "Google Sans", sans-serif';
      ctx.fillStyle = textColor;
      ctx.fillText(displayChar(item.char), x, y - 4);
      ctx.font = '10px "Roboto Mono", monospace';
      ctx.fillStyle = isDark ? '#9AA0A6' : '#5F6368';
      ctx.fillText(String(item.freq), x, y + 8);
    } else {
      ctx.font = 'bold 11px "Google Sans", sans-serif';
      ctx.fillStyle = isDark ? '#8AB4F8' : '#1A73E8';
      ctx.fillText('∑', x, y - 4);
      ctx.font = 'bold 10px "Roboto Mono", monospace';
      ctx.fillStyle = textColor;
      ctx.fillText(String(item.freq), x, y + 8);
    }

    // Badge above node
    if (isJustInserted) {
      drawBadge(ctx, x, y - r - 6, 'NEW', GREEN, '#FFFFFF');
    } else if (isRootDone) {
      drawBadge(ctx, x, y - r - 6, 'ROOT', YELLOW, '#000000');
    }

    ctx.restore();
  }

  function drawTreeNode(ctx, x, y, node, isHighlight, highlightTag, scale, isDark, textColor, bgSurface) {
    if (!node) return;
    const r = NODE_RADIUS * Math.max(0.01, scale);
    const isLeaf = !node.left && !node.right;

    ctx.save();
    ctx.beginPath();
    ctx.arc(x, y, r, 0, Math.PI * 2);

    if (isHighlight) {
      ctx.fillStyle = isDark ? '#2B2B1B' : '#FEF7E0';
      ctx.shadowColor = highlightTag === 'MIN 1' ? RED : (highlightTag === 'MIN 2' ? YELLOW : BLUE);
      ctx.shadowBlur = 18;
    } else {
      ctx.fillStyle = bgSurface;
      ctx.shadowColor = 'rgba(0,0,0,0.06)';
      ctx.shadowBlur = 6;
    }
    ctx.fill();

    ctx.shadowBlur = 0;
    if (isHighlight) {
      ctx.strokeStyle = highlightTag === 'MIN 1' ? RED : (highlightTag === 'MIN 2' ? YELLOW : BLUE);
      ctx.lineWidth = 3.0;
    } else {
      ctx.strokeStyle = isLeaf ? GREEN : (isDark ? '#5F6368' : '#BDC1C6');
      ctx.lineWidth = isLeaf ? 2.5 : 1.8;
    }
    ctx.stroke();

    // Node content
    if (scale > 0.4) {
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      if (isLeaf) {
        ctx.font = `bold ${Math.round(13 * scale)}px "Google Sans", sans-serif`;
        ctx.fillStyle = textColor;
        ctx.fillText(displayChar(node.char), x, y - 4 * scale);
        ctx.font = `${Math.round(10 * scale)}px "Roboto Mono", monospace`;
        ctx.fillStyle = isDark ? '#9AA0A6' : '#5F6368';
        ctx.fillText(String(node.freq), x, y + 9 * scale);
      } else {
        ctx.font = `bold ${Math.round(13 * scale)}px "Roboto Mono", monospace`;
        ctx.fillStyle = textColor;
        ctx.fillText(String(node.freq), x, y);
      }
    }

    // Highlight tag pill
    if (highlightTag && scale > 0.5) {
      const tagBg = highlightTag === 'MIN 1' ? RED : (highlightTag === 'MIN 2' ? YELLOW : BLUE);
      const tagColor = highlightTag === 'MIN 2' ? '#000000' : '#FFFFFF';
      drawBadge(ctx, x, y - r - 8, highlightTag, tagBg, tagColor);
    }

    ctx.restore();
  }

  function drawConstructionStep(step, progress) {
    if (!step) return;
    const ctx = treeCanvas.getContext('2d');
    const dpr = window.devicePixelRatio || 1;
    const w = treeCanvas.width / dpr;
    const h = treeCanvas.height / dpr;

    ctx.clearRect(0, 0, treeCanvas.width, treeCanvas.height);
    ctx.save();
    ctx.scale(dpr, dpr);

    const isDark = document.documentElement.getAttribute('data-theme') === 'dark';
    const textColor = isDark ? '#E8EAED' : '#202124';
    const subTextColor = isDark ? '#9AA0A6' : '#5F6368';
    const bgSurface = isDark ? '#16213E' : '#FFFFFF';
    const dockBg = isDark ? 'rgba(22, 33, 62, 0.94)' : 'rgba(248, 249, 250, 0.96)';
    const dockBorder = isDark ? 'rgba(66, 133, 244, 0.35)' : 'rgba(66, 133, 244, 0.22)';

    // ─── 1. PRIORITY QUEUE DOCK (Bottom Shelf) ───
    const dockH = 76;
    const dockY = h - dockH - 12;
    const dockX = 14;
    const dockW = w - 28;

    drawRoundRect(ctx, dockX, dockY, dockW, dockH, 12);
    ctx.fillStyle = dockBg;
    ctx.fill();
    ctx.strokeStyle = dockBorder;
    ctx.lineWidth = 1.5;
    ctx.stroke();

    // Dock title & subtitle
    ctx.font = '600 11px "Google Sans", sans-serif';
    ctx.fillStyle = isDark ? '#8AB4F8' : '#1A73E8';
    ctx.textAlign = 'left';
    ctx.fillText('MIN-HEAP PRIORITY QUEUE', dockX + 16, dockY + 18);

    ctx.font = '500 10px "Roboto Mono", monospace';
    ctx.fillStyle = subTextColor;
    ctx.textAlign = 'right';
    const queueSubtitle = (step.type === 'complete')
      ? 'Construction Complete — Root Node Remaining'
      : 'Sorted by Frequency (Ascending)';
    ctx.fillText(queueSubtitle, dockX + dockW - 16, dockY + 18);

    // Queue slots helper
    function getQueuePos(idx, total) {
      const sw = Math.min(68, (dockW - 36) / Math.max(total, 1));
      const sx = dockX + (dockW - total * sw) / 2 + sw / 2;
      return { x: sx + idx * sw, y: dockY + 46 };
    }

    const isExtractPhase = (step.type === 'merge' && progress < 0.85);
    const isInsertPhase = (step.type === 'merge' && progress >= 0.85);
    const activeQueue = isInsertPhase ? step.queueAfter : step.queueBefore;

    // Calculate motion for lifting nodes
    let min1Pos = null;
    let min2Pos = null;
    let parentPos = null;
    let parentScale = 0;
    let edgeDrawProgress = 0;

    if (step.type === 'merge') {
      const min1Node = nodeMap.get(step.min1.id);
      const min2Node = step.min2 ? nodeMap.get(step.min2.id) : null;
      const pNode = nodeMap.get(step.parent.id);

      const q1 = getQueuePos(0, step.queueBefore.length);
      const q2 = step.min2 ? getQueuePos(1, step.queueBefore.length) : q1;

      if (progress < 0.28) {
        // Phase 1: Highlighting in queue dock
        min1Pos = { x: q1.x, y: q1.y };
        min2Pos = { x: q2.x, y: q2.y };
        parentScale = 0;
        edgeDrawProgress = 0;
      } else if (progress < 0.72) {
        // Phase 2: Lifting up with bezier curve
        const u = (progress - 0.28) / (0.72 - 0.28);
        const e = easeInOutCubic(u);
        const arc = Math.sin(Math.PI * e) * 45;

        min1Pos = {
          x: q1.x + (min1Node.targetX - q1.x) * e,
          y: q1.y + (min1Node.targetY - q1.y) * e - arc,
        };
        if (min2Node) {
          min2Pos = {
            x: q2.x + (min2Node.targetX - q2.x) * e,
            y: q2.y + (min2Node.targetY - q2.y) * e - arc,
          };
        }
        parentPos = { x: pNode.targetX, y: pNode.targetY };
        parentScale = Math.max(0, Math.min(1, (u - 0.3) / 0.7));
        edgeDrawProgress = (progress >= 0.60) ? Math.max(0, Math.min(1, (progress - 0.60) / 0.25)) : 0;
      } else {
        // Phase 3 & 4: Settled in tree
        min1Pos = { x: min1Node.targetX, y: min1Node.targetY };
        min2Pos = min2Node ? { x: min2Node.targetX, y: min2Node.targetY } : null;
        parentPos = { x: pNode.targetX, y: pNode.targetY };
        parentScale = 1;
        edgeDrawProgress = (progress >= 0.60) ? Math.max(0, Math.min(1, (progress - 0.60) / 0.25)) : 1;
      }
    }

    // ─── 2. DRAW QUEUE ITEMS IN DOCK ───
    activeQueue.forEach((item, idx) => {
      // In merge lift phase, slot 0 and 1 are lifting into tree, so show dashed placeholder in dock
      if (isExtractPhase && (idx === 0 || (idx === 1 && step.min2))) {
        const pos = getQueuePos(idx, activeQueue.length);
        ctx.beginPath();
        ctx.arc(pos.x, pos.y, 18, 0, Math.PI * 2);
        ctx.strokeStyle = isDark ? '#3C4043' : '#DADCE0';
        ctx.lineWidth = 1.5;
        ctx.setLineDash([4, 4]);
        ctx.stroke();
        ctx.setLineDash([]);
        return;
      }

      const pos = getQueuePos(idx, activeQueue.length);
      const isJustInserted = isInsertPhase && (idx === step.insertIdx);
      const isRootDone = (step.type === 'complete' && idx === 0);

      drawQueueNode(ctx, pos.x, pos.y, item, {
        isJustInserted,
        isRootDone,
        isDark,
        textColor,
        bgSurface,
      });
    });

    // ─── 3. DRAW TREE WORKSPACE (Above Dock) ───
    ctx.save();
    ctx.translate(panOffset.x, panOffset.y);
    ctx.scale(zoomLevel, zoomLevel);

    // Draw previously established edges
    if (step.activeEdges && step.activeEdges.length > 0) {
      step.activeEdges.forEach(edge => {
        // Skip current step's new edges while they animate
        const isCurrentNewEdge = step.newEdges && step.newEdges.some(ne => ne.from === edge.from && ne.to === edge.to);
        if (isCurrentNewEdge && edgeDrawProgress < 1) return;

        const fromNode = nodeMap.get(edge.from);
        const toNode = nodeMap.get(edge.to);
        if (fromNode && toNode) {
          drawEdgeWithLabel(ctx, fromNode.targetX, fromNode.targetY, toNode.targetX, toNode.targetY, edge.bit, 1.0, isDark);
        }
      });
    }

    // Draw current animated edges
    if (step.type === 'merge' && edgeDrawProgress > 0 && parentPos) {
      if (min1Pos) {
        drawEdgeWithLabel(ctx, parentPos.x, parentPos.y, min1Pos.x, min1Pos.y, '0', edgeDrawProgress, isDark);
      }
      if (min2Pos) {
        drawEdgeWithLabel(ctx, parentPos.x, parentPos.y, min2Pos.x, min2Pos.y, '1', edgeDrawProgress, isDark);
      }
    }

    // Draw all settled tree nodes that belong in tree workspace
    if (step.activeNodes) {
      step.activeNodes.forEach(nodeId => {
        // Skip currently merging nodes while animating
        if (step.type === 'merge' && (nodeId === step.min1.id || (step.min2 && nodeId === step.min2.id) || (step.parent && nodeId === step.parent.id))) {
          return;
        }
        const node = nodeMap.get(nodeId);
        if (node) {
          drawTreeNode(ctx, node.targetX, node.targetY, node, false, false, 1.0, isDark, textColor, bgSurface);
        }
      });
    }

    // Draw lifting/merging nodes
    if (step.type === 'merge') {
      const min1Node = nodeMap.get(step.min1.id);
      const min2Node = step.min2 ? nodeMap.get(step.min2.id) : null;
      const pNode = nodeMap.get(step.parent.id);

      // Min 1
      if (min1Pos) {
        const isMin1HL = (progress < 0.28);
        drawTreeNode(ctx, min1Pos.x, min1Pos.y, min1Node, isMin1HL, 'MIN 1', 1.0, isDark, textColor, bgSurface);
      }
      // Min 2
      if (min2Pos && min2Node) {
        const isMin2HL = (progress < 0.28);
        drawTreeNode(ctx, min2Pos.x, min2Pos.y, min2Node, isMin2HL, 'MIN 2', 1.0, isDark, textColor, bgSurface);
      }
      // Parent
      if (parentPos && parentScale > 0) {
        drawTreeNode(ctx, parentPos.x, parentPos.y, pNode, true, false, parentScale, isDark, textColor, bgSurface);
      }
    } else if (step.type === 'complete' && huffmanRoot) {
      // Completed root celebration
      const rNode = nodeMap.get(huffmanRoot.id);
      if (rNode) {
        drawTreeNode(ctx, rNode.targetX, rNode.targetY, rNode, true, 'ROOT', 1.0, isDark, textColor, bgSurface);
      }
    }

    ctx.restore();
    ctx.restore();
  }

  /* ═══════════════════════════════════════════════════════════
     DECODING TREE CANVAS RENDERER
     ═══════════════════════════════════════════════════════════ */

  function drawTree(canvas, root, highlightPath = [], highlightNodeId = -1) {
    const ctx = canvas.getContext('2d');
    const dpr = window.devicePixelRatio || 1;
    const w = canvas.width / dpr, h = canvas.height / dpr;

    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.save();
    ctx.scale(dpr, dpr);

    if (!root) { ctx.restore(); return; }

    const isDark = document.documentElement.getAttribute('data-theme') === 'dark';
    const edgeColor = isDark ? '#555' : '#CCC';
    const textColor = isDark ? '#E8EAED' : '#202124';
    const bgSurface = isDark ? '#16213E' : '#FFFFFF';
    const bgSurfaceHighlight = isDark ? '#1E3A5F' : '#EFF5FF';

    // Draw edges
    function drawEdges(node) {
      if (!node) return;
      if (node.left) {
        const isHighlighted = highlightPath.some(e => e.from === node.id && e.to === node.left.id);
        ctx.beginPath();
        ctx.moveTo(node.x, node.y);
        ctx.lineTo(node.left.x, node.left.y);
        ctx.strokeStyle = isHighlighted ? BLUE : edgeColor;
        ctx.lineWidth = isHighlighted ? 3 : 1.5;
        ctx.stroke();

        const mx = (node.x + node.left.x) / 2 - 10;
        const my = (node.y + node.left.y) / 2 - 4;
        ctx.font = 'bold 13px "Roboto Mono", monospace';
        ctx.fillStyle = isHighlighted ? BLUE : (isDark ? '#6FA8F7' : '#4285F4');
        ctx.fillText('0', mx, my);

        drawEdges(node.left);
      }
      if (node.right) {
        const isHighlighted = highlightPath.some(e => e.from === node.id && e.to === node.right.id);
        ctx.beginPath();
        ctx.moveTo(node.x, node.y);
        ctx.lineTo(node.right.x, node.right.y);
        ctx.strokeStyle = isHighlighted ? RED : edgeColor;
        ctx.lineWidth = isHighlighted ? 3 : 1.5;
        ctx.stroke();

        const mx = (node.x + node.right.x) / 2 + 6;
        const my = (node.y + node.right.y) / 2 - 4;
        ctx.font = 'bold 13px "Roboto Mono", monospace';
        ctx.fillStyle = isHighlighted ? RED : (isDark ? '#F28B82' : '#EA4335');
        ctx.fillText('1', mx, my);

        drawEdges(node.right);
      }
    }
    drawEdges(root);

    // Draw nodes
    function drawNodes(node) {
      if (!node) return;
      drawNodes(node.left);
      drawNodes(node.right);

      const isLeaf = !node.left && !node.right;
      const isHL = node.id === highlightNodeId;
      const isOnPath = highlightPath.some(e => e.from === node.id || e.to === node.id);

      ctx.beginPath();
      ctx.arc(node.x, node.y, NODE_RADIUS, 0, Math.PI * 2);

      if (isHL) {
        ctx.fillStyle = YELLOW;
        ctx.shadowColor = YELLOW;
        ctx.shadowBlur = 16;
      } else if (isOnPath) {
        ctx.fillStyle = bgSurfaceHighlight;
        ctx.shadowColor = BLUE;
        ctx.shadowBlur = 8;
      } else {
        ctx.fillStyle = bgSurface;
        ctx.shadowColor = 'transparent';
        ctx.shadowBlur = 0;
      }
      ctx.fill();

      ctx.shadowBlur = 0;
      ctx.strokeStyle = isLeaf ? (isHL ? '#333' : GREEN) : (isHL ? '#333' : (isDark ? '#555' : '#CCC'));
      ctx.lineWidth = isLeaf ? 2.5 : 1.5;
      ctx.stroke();

      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      if (isLeaf) {
        ctx.font = 'bold 14px "Google Sans", sans-serif';
        ctx.fillStyle = isHL ? '#000' : textColor;
        ctx.fillText(displayChar(node.char), node.x, node.y - 4);
        ctx.font = '11px "Roboto Mono", monospace';
        ctx.fillStyle = isDark ? '#9AA0A6' : '#80868B';
        ctx.fillText(String(node.freq), node.x, node.y + 10);
      } else {
        ctx.font = '600 13px "Roboto Mono", monospace';
        ctx.fillStyle = isHL ? '#000' : textColor;
        ctx.fillText(String(node.freq), node.x, node.y);
      }
    }
    drawNodes(root);

    ctx.restore();
  }

  /* ═══════════════════════════════════════════════════════════
     DOM ELEMENTS & EVENT HANDLERS
     ═══════════════════════════════════════════════════════════ */

  const $ = (sel) => document.querySelector(sel);
  const $$ = (sel) => document.querySelectorAll(sel);

  const textInput = $('#text-input');
  const analyzeBtn = $('#analyze-btn');
  const freqPanel = $('#freq-panel');
  const freqBars = $('#freq-bars');
  const treeSection = $('#tree-section');
  const encodeSection = $('#encode-section');
  const decodeSection = $('#decode-section');
  const treeCanvas = $('#tree-canvas');
  const decodeTreeCanvas = $('#decode-tree-canvas');
  const heapNodesEl = $('#heap-nodes');
  const heapQueueCount = $('#heap-queue-count');
  const narrationStepTag = $('#narration-step-tag');
  const narrationText = $('#narration-text');
  const btnPlay = $('#btn-play');
  const btnStepFwd = $('#btn-step-fwd');
  const btnStepBack = $('#btn-step-back');
  const btnReset = $('#btn-reset');
  const btnSkip = $('#btn-skip');
  const speedSlider = $('#speed-slider');
  const speedLabel = $('#speed-label');
  const stepCurrent = $('#step-current');
  const stepTotal = $('#step-total');

  // Mode Switch & Banner Selectors
  const modeStandardBtn = $('#mode-standard-btn');
  const modeCanonicalBtn = $('#mode-canonical-btn');
  const modeDescPill = $('#mode-desc-pill');
  const effBanner = $('#efficiency-callout-banner');
  const bannerIcon = $('#banner-icon');
  const bannerTitle = $('#banner-title');
  const bannerBadge = $('#banner-badge');
  const bannerDesc = $('#banner-explanation');
  const bchipRaw = $('#bchip-raw');
  const bchipTotal = $('#bchip-total');
  const bchipDiff = $('#bchip-diff');
  const bchipRatio = $('#bchip-ratio');

  /* ─── Dark Mode Toggle ─── */
  const darkToggle = $('#dark-mode-toggle');
  darkToggle.addEventListener('click', () => {
    const html = document.documentElement;
    const next = html.getAttribute('data-theme') === 'dark' ? 'light' : 'dark';
    html.setAttribute('data-theme', next);
    localStorage.setItem('huffman-theme', next);
  });
  const savedTheme = localStorage.getItem('huffman-theme');
  if (savedTheme) document.documentElement.setAttribute('data-theme', savedTheme);

  /* ─── Presets ─── */
  $$('.preset-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      textInput.value = btn.dataset.text;
      analyzeBtn.click();
    });
  });

  /* ─── Tabs ─── */
  $$('.tab-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      $$('.tab-btn').forEach(b => b.classList.remove('active'));
      $$('.tab-content').forEach(c => c.classList.remove('active'));
      btn.classList.add('active');
      $(`#${btn.dataset.tab}`).classList.add('active');
    });
  });

  function resizeTreeCanvas() {
    const rect = treeCanvas.parentElement.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    treeCanvas.width = rect.width * dpr;
    treeCanvas.height = rect.height * dpr;
  }

  function resizeDecodeCanvas() {
    const rect = decodeTreeCanvas.parentElement.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    decodeTreeCanvas.width = rect.width * dpr;
    decodeTreeCanvas.height = rect.height * dpr;
  }

  /* ─── Frequency Rendering ─── */
  function renderFrequencyPanel(freq, total) {
    $('#stat-unique').textContent = freq.size;
    $('#stat-total').textContent = total;
    $('#stat-orig-bits').textContent = `${total * 8} bits`;

    const maxFreq = Math.max(...freq.values());
    const sorted = [...freq.entries()].sort((a, b) => b[1] - a[1]);

    freqBars.innerHTML = '';
    sorted.forEach(([char, f], i) => {
      const pct = (f / maxFreq) * 100;
      const color = COLORS[i % COLORS.length];
      const div = document.createElement('div');
      div.className = 'freq-bar-item';
      div.style.animationDelay = `${i * 60}ms`;
      div.innerHTML = `
        <span class="bar-freq">${f}</span>
        <div class="bar" style="height:${pct}%;background:${color}"></div>
        <span class="bar-label">${displayChar(char)}</span>
      `;
      freqBars.appendChild(div);
    });
  }

  /* ─── HTML Heap Queue Rendering ─── */
  function renderHeapQueue(step, progress) {
    heapNodesEl.innerHTML = '';
    if (!step) return;

    const queue = (progress >= 0.85 || step.type === 'complete') ? step.queueAfter : step.queueBefore;
    const isExtractPhase = (progress < 0.85 && step.type === 'merge');
    const isInsertPhase = (progress >= 0.85 && step.type === 'merge');

    queue.forEach((n, idx) => {
      const el = document.createElement('div');
      el.className = 'heap-node';

      if (isExtractPhase && step.min1 && n.id === step.min1.id) {
        el.classList.add('min-1');
        const badge = document.createElement('span');
        badge.className = 'node-min-badge';
        badge.textContent = 'MIN 1';
        el.appendChild(badge);
      } else if (isExtractPhase && step.min2 && n.id === step.min2.id) {
        el.classList.add('min-2');
        const badge = document.createElement('span');
        badge.className = 'node-min-badge';
        badge.textContent = 'MIN 2';
        el.appendChild(badge);
      } else if (isInsertPhase && step.parent && n.id === step.parent.id) {
        el.classList.add('merged');
        const badge = document.createElement('span');
        badge.className = 'node-min-badge';
        badge.style.background = 'var(--g-green)';
        badge.textContent = 'NEW';
        el.appendChild(badge);
      } else if (step.type === 'complete' && idx === 0) {
        el.classList.add('merged');
        const badge = document.createElement('span');
        badge.className = 'node-min-badge';
        badge.style.background = 'var(--g-yellow)';
        badge.style.color = '#000';
        badge.textContent = 'ROOT';
        el.appendChild(badge);
      }

      const charSpan = document.createElement('span');
      charSpan.className = 'node-char';
      charSpan.textContent = n.char ? displayChar(n.char) : '⊕';
      el.appendChild(charSpan);

      const freqSpan = document.createElement('span');
      freqSpan.className = 'node-freq';
      freqSpan.textContent = n.freq;
      el.appendChild(freqSpan);

      heapNodesEl.appendChild(el);
    });
  }

  /* ═══════════════════════════════════════════════════════════
     STEP-BY-STEP PLAYBACK CONTROLLERS
     ═══════════════════════════════════════════════════════════ */

  function updateStepUI() {
    stepCurrent.textContent = currentStep;
    stepTotal.textContent = Math.max(0, buildSteps.length - 1);

    const step = buildSteps[currentStep];
    if (!step) return;

    if (narrationStepTag) narrationStepTag.textContent = step.badge;
    if (narrationText) narrationText.innerHTML = step.description;

    const q = (stepProgress >= 0.85 || step.type === 'complete') ? step.queueAfter : step.queueBefore;
    if (heapQueueCount) heapQueueCount.textContent = `${q.length} items`;

    renderHeapQueue(step, stepProgress);
  }

  function startStepAnimation() {
    stepProgress = 0.0;
    isAnimating = true;
    updateStepUI();
  }

  function onStepSettled() {
    updateStepUI();

    const isLast = (currentStep >= buildSteps.length - 1);
    if (isLast) {
      stopPlayback();
      showEncodingTable();
      showDecodeSection();
      return;
    }

    if (isPlaying) {
      const settlePause = 420 / speedMultiplier;
      playDelayTimeout = setTimeout(() => {
        if (!isPlaying) return;
        currentStep++;
        startStepAnimation();
      }, settlePause);
    }
  }

  function startPlayback() {
    if (currentStep >= buildSteps.length - 1) {
      currentStep = 0;
      stepProgress = 0.0;
    }
    isPlaying = true;
    btnPlay.classList.add('playing');
    startStepAnimation();
  }

  function stopPlayback() {
    isPlaying = false;
    btnPlay.classList.remove('playing');
    if (playDelayTimeout) {
      clearTimeout(playDelayTimeout);
      playDelayTimeout = null;
    }
  }

  function stepForward() {
    stopPlayback();
    if (currentStep < buildSteps.length - 1) {
      currentStep++;
      startStepAnimation();
    }
  }

  function stepBack() {
    stopPlayback();
    if (currentStep > 0) {
      currentStep--;
      stepProgress = 1.0;
      isAnimating = false;
      updateStepUI();
    }
  }

  function resetConstruction() {
    stopPlayback();
    currentStep = 0;
    stepProgress = 1.0;
    isAnimating = false;
    updateStepUI();
    encodeSection.classList.add('hidden');
    decodeSection.classList.add('hidden');
  }

  btnPlay.addEventListener('click', () => {
    if (isPlaying) stopPlayback();
    else startPlayback();
  });

  btnStepFwd.addEventListener('click', stepForward);
  btnStepBack.addEventListener('click', stepBack);
  btnReset.addEventListener('click', resetConstruction);

  if (btnSkip) {
    btnSkip.addEventListener('click', () => {
      stopPlayback();
      if (!buildSteps || buildSteps.length === 0) return;
      currentStep = buildSteps.length - 1;
      stepProgress = 1.0;
      isAnimating = false;
      onStepSettled();
    });
  }

  speedSlider.addEventListener('input', () => {
    speedMultiplier = parseFloat(speedSlider.value);
    speedLabel.textContent = `${speedMultiplier}×`;
  });

  /* ─── Analyze Button ─── */
  analyzeBtn.addEventListener('click', () => {
    const text = textInput.value;
    if (!text.trim()) return;
    inputText = text;

    stopPlayback();
    stopDecoding();

    // 1. Build frequency map
    freqMap = buildFrequencyMap(text);
    renderFrequencyPanel(freqMap, text.length);
    freqPanel.classList.remove('hidden');

    // 2. Build Huffman tree and record step-by-step actions
    huffmanRoot = buildHuffmanTree(freqMap);
    codes = assignCodes(huffmanRoot);

    // 3. Show tree section and layout coordinates
    treeSection.classList.remove('hidden');
    treeSection.scrollIntoView({ behavior: 'smooth', block: 'start' });

    resizeTreeCanvas();
    const dpr = window.devicePixelRatio || 1;
    treeNodes = layoutTree(huffmanRoot, treeCanvas.width / dpr, treeCanvas.height / dpr);

    // 4. Initialize at Step 0 (initial queue) — NOT rendered instantly!
    currentStep = 0;
    stepProgress = 1.0;
    isAnimating = false;
    panOffset = { x: 0, y: 0 };
    zoomLevel = 1;
    updateStepUI();

    // Hide encode/decode sections until tree construction is completed
    encodeSection.classList.add('hidden');
    decodeSection.classList.add('hidden');
  });

  /* ═══════════════════════════════════════════════════════════
     ENCODING TABLE & ANALYTICS
     ═══════════════════════════════════════════════════════════ */

  function showEncodingTable() {
    encodeSection.classList.remove('hidden');
    const tbody = $('#code-table-body');
    tbody.innerHTML = '';

    let totalOrigBits = inputText.length * 8;
    let totalEncodedBits = 0;

    const sorted = [...freqMap.entries()].sort((a, b) => b[1] - a[1]);

    sorted.forEach(([char, freq]) => {
      const code = codes[char] || '';
      const codeBits = code.length;
      const charBits = 8;
      const totalBitsForChar = codeBits * freq;
      const origBitsForChar = charBits * freq;
      const saved = origBitsForChar - totalBitsForChar;
      totalEncodedBits += totalBitsForChar;

      const bitsHtml = [...code].map(b => `<span class="code-bit b${b}">${b}</span>`).join('');
      const asciiStr = char.charCodeAt(0).toString(2).padStart(8, '0');
      const asciiBitsHtml = [...asciiStr].map(b => `<span class="code-bit b${b}">${b}</span>`).join('');

      const tr = document.createElement('tr');
      tr.innerHTML = `
        <td><strong>${displayChar(char)}</strong></td>
        <td><span class="code-bits">${asciiBitsHtml}</span></td>
        <td><span class="code-bits">${bitsHtml}</span></td>
        <td>${codeBits}</td>
        <td>${freq}</td>
        <td class="${saved >= 0 ? 'bits-saved-positive' : 'bits-saved-negative'}">${saved >= 0 ? '+' : ''}${saved}</td>
      `;
      tbody.appendChild(tr);
    });

    updateAnalyticsUI();

    const encoded = encodeText(inputText, codes);
    const bsEl = $('#encoded-bitstring');
    bsEl.innerHTML = [...encoded].map((b, i) =>
      `<span class="bit-${b}" data-idx="${i}">${b}</span>`
    ).join('');

    setTimeout(() => {
      encodeSection.scrollIntoView({ behavior: 'smooth', block: 'start' });
    }, 250);
  }

  function updateAnalyticsUI() {
    if (!inputText || freqMap.size === 0) return;

    const totalOrigBits = inputText.length * 8;
    let totalPayloadBits = 0;

    for (const [char, freq] of freqMap) {
      const code = codes[char] || '';
      totalPayloadBits += freq * code.length;
    }

    const isStandard = (overheadMode === 'standard');
    // Standard Mode: 8 bits char ASCII map + 8 bits frequency/tree metadata per unique symbol
    const overheadBits = isStandard ? (freqMap.size * 16) : 0;
    const totalCompressed = totalPayloadBits + overheadBits;
    const netSaved = totalOrigBits - totalCompressed;
    const ratio = totalOrigBits > 0 ? ((totalOrigBits - totalCompressed) / totalOrigBits) * 100 : 0;

    // 1. Update Mode Toggle Buttons
    if (modeStandardBtn && modeCanonicalBtn) {
      modeStandardBtn.classList.toggle('active', isStandard);
      modeStandardBtn.setAttribute('aria-checked', isStandard ? 'true' : 'false');
      modeCanonicalBtn.classList.toggle('active', !isStandard);
      modeCanonicalBtn.setAttribute('aria-checked', !isStandard ? 'true' : 'false');
    }

    if (modeDescPill) {
      if (isStandard) {
        modeDescPill.innerHTML = `<strong>Standard Mode Active:</strong> Includes payload bits plus full header serialization overhead (<strong>${freqMap.size} unique symbols × 16 bits</strong> = ${overheadBits} bits: 8-bit ASCII character map + 8-bit frequency/code length metadata per symbol).`;
      } else {
        modeDescPill.innerHTML = `<strong>Canonical / Payload-Only Mode Active:</strong> Assumes a pre-shared dictionary tree or canonical bit-length array (<strong>0 bits header overhead</strong>), reflecting raw variable-length prefix code payload efficiency.`;
      }
    }

    const calcSubtitle = $('#calc-panel-subtitle');
    if (calcSubtitle) {
      calcSubtitle.textContent = isStandard
        ? 'Standard Mode (Payload + Header Overhead)'
        : 'Canonical / Payload-Only Mode (Zero Header)';
    }

    // 2. Update Breakdown Table
    const elRaw = $('#calc-orig');
    const elPayload = $('#calc-encoded');
    const elOverhead = $('#calc-overhead');
    const elTotal = $('#calc-total');
    const elRatio = $('#calc-ratio');

    if (elRaw) elRaw.textContent = `${totalOrigBits} bits`;
    if (elPayload) elPayload.textContent = `${totalPayloadBits} bits`;
    if (elOverhead) elOverhead.textContent = `${overheadBits} bits`;
    if (elTotal) elTotal.textContent = `${totalCompressed} bits`;
    if (elRatio) {
      elRatio.textContent = `${ratio >= 0 ? '+' : ''}${ratio.toFixed(1)}%`;
      elRatio.className = `metric-pct metric-bold ${ratio >= 0 ? 'text-success' : 'text-warning'}`;
    }

    const elPayloadPct = $('#breakdown-payload-pct');
    const elOverheadPct = $('#breakdown-overhead-pct');
    const elTotalPct = $('#breakdown-total-pct');
    if (elPayloadPct) elPayloadPct.textContent = totalOrigBits > 0 ? `${((totalPayloadBits / totalOrigBits) * 100).toFixed(1)}%` : '—';
    if (elOverheadPct) elOverheadPct.textContent = totalOrigBits > 0 ? `${((overheadBits / totalOrigBits) * 100).toFixed(1)}%` : '—';
    if (elTotalPct) elTotalPct.textContent = totalOrigBits > 0 ? `${((totalCompressed / totalOrigBits) * 100).toFixed(1)}%` : '—';

    const elOverheadFormula = $('#breakdown-overhead-formula');
    if (elOverheadFormula) {
      elOverheadFormula.innerHTML = isStandard
        ? `<code>${freqMap.size} symbols × 16 bits (Char map + Tree metadata)</code>`
        : `<code>0 bits (Pre-shared / canonical payload-only)</code>`;
    }

    const elNetDiff = $('#breakdown-net-diff');
    const rowNet = $('#row-net-diff');
    const bulletNet = $('#bullet-net');

    if (elNetDiff) {
      if (netSaved >= 0) {
        elNetDiff.innerHTML = `<span class="net-badge positive">+${netSaved} bits saved</span>`;
      } else {
        elNetDiff.innerHTML = `<span class="net-badge negative">-${Math.abs(netSaved)} bits expansion</span>`;
      }
    }
    if (rowNet) {
      rowNet.classList.toggle('negative', netSaved < 0);
    }
    if (bulletNet) {
      bulletNet.classList.toggle('negative', netSaved < 0);
    }

    // 3. Update Dynamic Efficiency & Overhead Warning Banner
    if (effBanner) {
      effBanner.classList.remove('hidden');
      if (ratio < 0) {
        effBanner.className = 'efficiency-banner warning-banner';
        if (bannerIcon) {
          bannerIcon.innerHTML = `
            <svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
              <path d="M10.29 3.86L1.82 18a2 2 0 0 0 1.71 3h16.94a2 2 0 0 0 1.71-3L13.71 3.86a2 2 0 0 0-3.42 0z"/>
              <line x1="12" y1="9" x2="12" y2="13"/>
              <line x1="12" y1="17" x2="12.01" y2="17"/>
            </svg>`;
        }
        if (bannerTitle) bannerTitle.textContent = 'Heads Up: Compression Inefficient / Not Feasible for this input';
        if (bannerBadge) {
          bannerBadge.className = 'banner-status-tag tag-warning';
          bannerBadge.textContent = `Negative Compression (${ratio.toFixed(1)}%)`;
        }
        if (bannerDesc) {
          bannerDesc.textContent = 'Due to small input size or large unique character count, table overhead exceeds bit savings. In production systems, data would be stored uncompressed (Raw Store Mode). However, the Huffman Tree construction and decoding traversal below will still run for educational purposes.';
        }
        if (bchipRaw) bchipRaw.innerHTML = `Raw: <strong>${totalOrigBits} bits</strong>`;
        if (bchipTotal) bchipTotal.innerHTML = `Compressed: <strong>${totalCompressed} bits</strong>`;
        if (bchipDiff) bchipDiff.innerHTML = `Difference: <strong>-${Math.abs(netSaved)} bits expansion</strong>`;
        if (bchipRatio) bchipRatio.innerHTML = `Ratio: <strong>${ratio.toFixed(1)}%</strong>`;
      } else {
        effBanner.className = 'efficiency-banner success-banner';
        if (bannerIcon) {
          bannerIcon.innerHTML = `
            <svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
              <path d="M22 11.08V12a10 10 0 1 1-5.93-9.14"/>
              <polyline points="22 4 12 14.01 9 11.01"/>
            </svg>`;
        }
        if (bannerTitle) bannerTitle.textContent = `Efficient Compression: Saved ${ratio.toFixed(1)}% bits`;
        if (bannerBadge) {
          bannerBadge.className = 'banner-status-tag tag-success';
          bannerBadge.textContent = `Efficient Compression (+${ratio.toFixed(1)}%)`;
        }
        if (bannerDesc) {
          bannerDesc.textContent = `Huffman coding achieved effective data reduction! Variable-length prefix codes mapped higher-frequency symbols to shorter bit sequences, saving ${netSaved} bits compared to uncompressed 8-bit ASCII storage (${totalOrigBits} raw → ${totalCompressed} compressed).`;
        }
        if (bchipRaw) bchipRaw.innerHTML = `Raw: <strong>${totalOrigBits} bits</strong>`;
        if (bchipTotal) bchipTotal.innerHTML = `Compressed: <strong>${totalCompressed} bits</strong>`;
        if (bchipDiff) bchipDiff.innerHTML = `Difference: <strong>+${netSaved} bits saved</strong>`;
        if (bchipRatio) bchipRatio.innerHTML = `Ratio: <strong>+${ratio.toFixed(1)}%</strong>`;
      }
    }

    // 4. Update Visual Gauge / Bar
    const ratioFill = $('#ratio-fill');
    const ratioSummary = $('#ratio-summary-badge');
    const legendOverhead = $('#legend-overhead-item');
    if (legendOverhead) {
      legendOverhead.style.display = isStandard ? 'inline-flex' : 'none';
    }

    if (ratio < 0) {
      if (ratioFill) {
        ratioFill.style.width = '100%';
        ratioFill.style.background = 'linear-gradient(90deg, #FBBC05, #EA4335)';
      }
      if (ratioSummary) {
        ratioSummary.className = 'ratio-summary-badge negative';
        ratioSummary.textContent = `Expanded by +${Math.abs(netSaved)} bits (${((totalCompressed / totalOrigBits) * 100).toFixed(1)}% of raw)`;
      }
    } else {
      if (ratioFill) {
        const fillPct = Math.max(5, Math.min(100, (totalCompressed / totalOrigBits) * 100));
        ratioFill.style.width = `${fillPct}%`;
        ratioFill.style.background = 'linear-gradient(90deg, #34A853, #4285F4)';
      }
      if (ratioSummary) {
        ratioSummary.className = 'ratio-summary-badge positive';
        ratioSummary.textContent = `Saved ${ratio.toFixed(1)}% (${netSaved} bits saved)`;
      }
    }

    // 5. Update Bitstring length badge
    const encoded = encodeText(inputText, codes);
    const bitstringBadge = $('#bitstring-len-badge');
    if (bitstringBadge) {
      bitstringBadge.textContent = `${encoded.length} bits payload`;
    }
  }

  // Overhead mode toggle button handlers
  if (modeStandardBtn) {
    modeStandardBtn.addEventListener('click', () => {
      if (overheadMode === 'standard') return;
      overheadMode = 'standard';
      updateAnalyticsUI();
    });
  }

  if (modeCanonicalBtn) {
    modeCanonicalBtn.addEventListener('click', () => {
      if (overheadMode === 'canonical') return;
      overheadMode = 'canonical';
      updateAnalyticsUI();
    });
  }

  /* ═══════════════════════════════════════════════════════════
     DECODING TRAVERSAL ANIMATION
     ═══════════════════════════════════════════════════════════ */

  function showDecodeSection() {
    decodeSection.classList.remove('hidden');
    resetDecoding();

    const encoded = encodeText(inputText, codes);
    const bsEl = $('#decode-bitstream');
    bsEl.innerHTML = [...encoded].map((b, i) =>
      `<span class="bit-${b}" data-idx="${i}" id="dbit-${i}">${b}</span>`
    ).join('');

    $('#decode-output').innerHTML = '';

    resizeDecodeCanvas();
    const dpr = window.devicePixelRatio || 1;
    const dw = decodeTreeCanvas.width / dpr;
    const dh = decodeTreeCanvas.height / dpr;
    layoutTreeForDecode(huffmanRoot, dw, dh);
    drawTree(decodeTreeCanvas, huffmanRoot);
  }

  function layoutTreeForDecode(root, w, h) {
    if (!root) return;
    function depth(n) { return n ? 1 + Math.max(depth(n.left), depth(n.right)) : 0; }
    const treeDepth = depth(root);
    const levelHeight = Math.min(65, (h - 80) / Math.max(treeDepth, 1));
    const baseSpread = Math.min(w * 0.38, 280);

    function layout(node, cx, cy, spread) {
      if (!node) return;
      node.x = node.targetX = cx;
      node.y = node.targetY = cy;
      layout(node.left, cx - spread, cy + levelHeight, spread * 0.52);
      layout(node.right, cx + spread, cy + levelHeight, spread * 0.52);
    }
    layout(root, w / 2, 45, baseSpread);
  }

  const decodePlayBtn = $('#decode-play');
  const decodePauseBtn = $('#decode-pause');
  const decodeResetBtn = $('#decode-reset');
  const decodeSpeedSlider = $('#decode-speed');
  const decodeSpeedLabel = $('#decode-speed-label');

  decodeSpeedSlider.addEventListener('input', () => {
    decodeSpeed = parseFloat(decodeSpeedSlider.value);
    decodeSpeedLabel.textContent = `${decodeSpeed}×`;
  });

  decodePlayBtn.addEventListener('click', () => {
    if (isDecoding) return;
    startDecoding();
  });

  decodePauseBtn.addEventListener('click', () => {
    stopDecoding();
  });

  decodeResetBtn.addEventListener('click', () => {
    stopDecoding();
    resetDecoding();
    showDecodeSection();
  });

  function startDecoding() {
    isDecoding = true;
    decodePlayBtn.classList.add('hidden');
    decodePauseBtn.classList.remove('hidden');
    decodeCurrentNode = huffmanRoot;
    decodeHighlightPath = [];
    decodeNextBit();
  }

  function stopDecoding() {
    isDecoding = false;
    decodePlayBtn.classList.remove('hidden');
    decodePauseBtn.classList.add('hidden');
    if (decodeTimer) { clearTimeout(decodeTimer); decodeTimer = null; }
  }

  function resetDecoding() {
    stopDecoding();
    decodeIndex = 0;
    decodedText = '';
    decodeCurrentNode = huffmanRoot;
    decodeHighlightPath = [];
  }

  function decodeNextBit() {
    if (!isDecoding) return;

    const encoded = encodeText(inputText, codes);
    if (decodeIndex >= encoded.length) {
      stopDecoding();
      return;
    }

    const bit = encoded[decodeIndex];

    for (let i = 0; i < decodeIndex; i++) {
      const el = document.getElementById(`dbit-${i}`);
      if (el) el.classList.add('bit-consumed');
    }
    const curBitEl = document.getElementById(`dbit-${decodeIndex}`);
    if (curBitEl) { curBitEl.classList.add('bit-active'); }

    const prevNode = decodeCurrentNode;
    if (bit === '0') {
      decodeCurrentNode = decodeCurrentNode.left;
    } else {
      decodeCurrentNode = decodeCurrentNode.right;
    }

    decodeHighlightPath.push({ from: prevNode.id, to: decodeCurrentNode.id });
    drawTree(decodeTreeCanvas, huffmanRoot, decodeHighlightPath, decodeCurrentNode.id);

    if (!decodeCurrentNode.left && !decodeCurrentNode.right) {
      decodedText += decodeCurrentNode.char;
      const outEl = $('#decode-output');
      const span = document.createElement('span');
      span.className = 'decoded-char';
      span.textContent = decodeCurrentNode.char;
      outEl.appendChild(span);

      decodeCurrentNode = huffmanRoot;
      decodeHighlightPath = [];
    }

    decodeIndex++;

    if (curBitEl) {
      setTimeout(() => {
        curBitEl.classList.remove('bit-active');
        curBitEl.classList.add('bit-consumed');
      }, 200 / decodeSpeed);
    }

    const delay = 320 / decodeSpeed;
    decodeTimer = setTimeout(decodeNextBit, delay);
  }

  /* ═══════════════════════════════════════════════════════════
     TREE CANVAS ZOOM & PAN (Tree nodes are strictly non-draggable)
     ═══════════════════════════════════════════════════════════ */

  $('#zoom-in').addEventListener('click', () => { zoomLevel = Math.min(3, zoomLevel + 0.2); });
  $('#zoom-out').addEventListener('click', () => { zoomLevel = Math.max(0.3, zoomLevel - 0.2); });
  $('#zoom-fit').addEventListener('click', () => { zoomLevel = 1; panOffset = { x: 0, y: 0 }; });

  treeCanvas.parentElement.addEventListener('wheel', (e) => {
    e.preventDefault();
    const delta = e.deltaY > 0 ? -0.1 : 0.1;
    zoomLevel = Math.min(3, Math.max(0.3, zoomLevel + delta));
  }, { passive: false });

  // Panning on background drag (No tree node dragging!)
  treeCanvas.parentElement.addEventListener('mousedown', (e) => {
    // Only pan if not clicking a button
    if (e.target.tagName === 'BUTTON') return;
    isPanning = true;
    panStart = { x: e.clientX - panOffset.x, y: e.clientY - panOffset.y };
  });

  window.addEventListener('mousemove', (e) => {
    if (isPanning) {
      panOffset.x = e.clientX - panStart.x;
      panOffset.y = e.clientY - panStart.y;
    }
  });

  window.addEventListener('mouseup', () => {
    isPanning = false;
  });

  /* ═══════════════════════════════════════════════════════════
     MAIN ANIMATION LOOP (60fps requestAnimationFrame)
     ═══════════════════════════════════════════════════════════ */

  let lastTime = performance.now();

  function mainLoop(timestamp) {
    const dt = Math.min((timestamp - lastTime) / 1000, 0.05);
    lastTime = timestamp;

    // Step animation progress
    if (isAnimating && buildSteps.length > 0) {
      const stepDurationMs = 1800 / speedMultiplier;
      stepProgress += (dt * 1000) / stepDurationMs;

      if (stepProgress >= 1.0) {
        stepProgress = 1.0;
        isAnimating = false;
        onStepSettled();
      } else {
        // Refresh HTML queue on phase boundaries for seamless sync
        if (Math.abs(stepProgress - 0.28) < 0.03 || Math.abs(stepProgress - 0.85) < 0.03) {
          updateStepUI();
        }
      }
    }

    // Render tree construction step if visible
    if (!treeSection.classList.contains('hidden') && buildSteps.length > 0 && currentStep >= 0 && currentStep < buildSteps.length) {
      drawConstructionStep(buildSteps[currentStep], stepProgress);
    }

    requestAnimationFrame(mainLoop);
  }

  /* ═══════════════════════════════════════════════════════════
     INITIALIZATION
     ═══════════════════════════════════════════════════════════ */

  function init() {
    window.addEventListener('resize', () => {
      if (!treeSection.classList.contains('hidden')) {
        resizeTreeCanvas();
        if (huffmanRoot) {
          const dpr = window.devicePixelRatio || 1;
          treeNodes = layoutTree(huffmanRoot, treeCanvas.width / dpr, treeCanvas.height / dpr);
        }
      }
    });

    requestAnimationFrame(mainLoop);
  }

  init();

})();
