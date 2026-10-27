module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3Chain
public import CFSG.Quasithin.H13.A5M22HatInputs

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.H13.A5.M22Hat CFSG.Quasithin.H.Mathieu

@[expose] def decW (n : ℕ) : List Bool :=
  (List.range (Nat.log2 n)).reverse.map fun i => n.testBit i

@[expose] def wordArr (a b : Array ℕ) : List Bool → Array ℕ
  | [] => id24
  | z :: w => comp24 (if z then b else a) (wordArr a b w)

@[expose] def cosArr (a b : Array ℕ) (ws : List (List Bool)) : Array (Array ℕ) :=
  (ws.map (wordArr a b)).toArray

@[expose] def piArr (ts : Array (Array ℕ)) (g : Array ℕ) (p : ℕ) : Array ℕ :=
  let pts := ts.map (·[p]!)
  ts.map fun t => (pts.findIdx? (· == (comp24 g t)[p]!)).getD 0

@[expose] def hArr (ts : Array (Array ℕ)) (g : Array ℕ) (pi : Array ℕ) : Array (Array ℕ) :=
  (Array.range ts.size).map fun k => comp24 (comp24 (invArr ts[pi[k]!]!) g) ts[k]!

@[expose] def piOK (ts : Array (Array ℕ)) (g : Array ℕ) (p : ℕ) (pi : Array ℕ) : Bool :=
  (List.range ts.size).all fun k =>
    pi[k]! < ts.size && (ts[pi[k]!]!)[p]! == (comp24 g ts[k]!)[p]!

@[expose] def cosetOK (a b : Array ℕ) (ts : Array (Array ℕ)) (m p : ℕ) : Bool :=
  ts.size == m &&
    ((List.range m).all fun k => (List.range m).all fun k' =>
      k == k' || (ts[k]!)[p]! != (ts[k']!)[p]!) &&
    piOK ts a p (piArr ts a p) && piOK ts b p (piArr ts b p) &&
    (List.range m).all fun k => (List.range 24).all fun j => (invArr ts[k]!)[(ts[k]!)[j]!]! == j

@[expose] def indCols (d : ℕ) (Xc : Array ℕ → ℕ → ℕ) (ts : Array (Array ℕ)) (g : Array ℕ)
    (p : ℕ) : List ℕ :=
  let pi := piArr ts g p
  let hs := hArr ts g pi
  (List.range (ts.size * d)).map fun j => Xc hs[j / d]! (1 <<< (j % d)) <<< (d * pi[j / d]!)

@[expose] def invStep (n : ℕ) (st : Array (ℕ × ℕ)) (i : ℕ) : Array (ℕ × ℕ) :=
  match (List.range n).find? (fun j => i ≤ j && (st[j]!).1.testBit i) with
  | none => st
  | some j =>
    let st' := st.swapIfInBounds i j
    let piv := st'[i]!
    st'.mapIdx fun j' e => if j' != i && e.1.testBit i then (e.1 ^^^ piv.1, e.2 ^^^ piv.2) else e

@[expose] def invCols (n : ℕ) (P : List ℕ) : List ℕ :=
  let st : Array (ℕ × ℕ) := (Array.range n).map fun j => (P.getD j 0, 1 <<< j)
  ((List.range n).foldl (invStep n) st).toList.map (·.2)

@[expose] def baseOK (N : ℕ) (P Pi : List ℕ) : Bool :=
  (List.range N).all (fun j => papply N Pi (P.getD j 0) == 1 <<< j) &&
    (List.range N).all fun j => papply N P (Pi.getD j 0) == 1 <<< j

@[expose] def conjCols (N : ℕ) (Pi K P : List ℕ) : List ℕ :=
  (List.range N).map fun j => papply N Pi (papply N K (P.getD j 0))

@[expose] def nsOf (dim : ℕ → ℕ) : List ℕ → ℕ → List ℕ
  | [], a => [a]
  | t :: ts, a => a :: nsOf dim ts (a + dim t)

@[expose] def nsOK (N : ℕ) (ns : List ℕ) : Bool :=
  decide (2 ≤ ns.length) && ns.getD 0 0 == 0 && ns.getD (ns.length - 1) 0 == N &&
    (List.range (ns.length - 1)).all fun i => ns.getD i 0 < ns.getD (i + 1) 0

@[expose] def flagSide (ns : List ℕ) (blk : ℕ → List ℕ) (M : List ℕ) : Bool :=
  (List.range ns.length).all (fun i => (List.range (ns.getD i 0)).all fun j =>
      M.getD j 0 < 2 ^ ns.getD i 0) &&
    (List.range (ns.length - 1)).all fun i =>
      blkCols M (ns.getD i 0) (ns.getD (i + 1) 0 - ns.getD i 0) == blk i

@[expose] def flagCore (N : ℕ) (K : Bool → List ℕ) (P Pi : List ℕ) (ns : List ℕ)
    (blk : ℕ → Bool → List ℕ) : Bool :=
  baseOK N P Pi && nsOK N ns &&
    flagSide ns (fun i => blk i false) (conjCols N Pi (K false) P) &&
    flagSide ns (fun i => blk i true) (conjCols N Pi (K true) P)

@[expose] def flagOK (N : ℕ) (K : Bool → List ℕ) (P : List ℕ) (ns : List ℕ)
    (blk : ℕ → Bool → List ℕ) : Bool :=
  flagCore N K P (invCols N P) ns blk

@[expose] def nortonCore (d : ℕ) (cols : Bool → List ℕ) (aC rows : List ℕ)
    (kers : List (ℕ × List (List Bool) × List ℕ)) (psi : ℕ) (rCols minv : List ℕ) : Bool :=
  ((0 :: kers.map (·.1)).all fun x => (0 :: kers.map (·.1)).all fun y =>
      (0 :: kers.map (·.1)).contains (x ^^^ y)) &&
    (List.range d).all (fun k => (0 :: kers.map (·.1)).contains
      ((1 <<< k) ^^^ papply d rCols (aC.getD k 0))) &&
    kers.all (kerCertOK d cols aC) &&
    (List.range d).all (fun k => !(dotb d psi (aC.getD k 0))) &&
    (List.range d).all fun k =>
      papply d minv (ofBits d fun l => (rows.getD l 0).testBit k) == 1 <<< k

@[expose] def nortonFastOK (d : ℕ) (cols : Bool → List ℕ) (aW : List (List Bool))
    (kers : List (ℕ × List (List Bool) × List ℕ)) (psi : ℕ) (dw : List (List Bool))
    (rCols minv : List ℕ) : Bool :=
  nortonCore d cols (aColsOf d cols aW) ((List.range d).map (rowAt d cols psi dw)) kers psi rCols
    minv

@[expose] def pApply (d : ℕ) (cols : Bool → List ℕ) (p : List (List Bool)) (v : ℕ) : ℕ :=
  p.foldl (fun acc w => acc ^^^ wapp d cols w v) 0

@[expose] def homZeroOK (d : ℕ) (A B : Bool → List ℕ) (u : ℕ) (gw : List (List Bool))
    (masks : List ℕ) (p₁ p₂ : List (List Bool)) (L₁ L₂ : List ℕ) : Bool :=
  pApply d A p₁ u == 0 && pApply d A p₂ u == 0 &&
    (List.range d).all (fun k => xorSelW d A gw u (masks.getD k 0) == 1 <<< k) &&
    (List.range d).all fun k =>
      (papply d L₁ (pApply d B p₁ (1 <<< k)) ^^^ papply d L₂ (pApply d B p₂ (1 <<< k))) == 1 <<< k

@[expose] def packCols {n : ℕ} (t : Vector (Vector (ZMod 2) n) n) : List ℕ :=
  (List.finRange n).map fun j => ofBits n fun i => if h : i < n then t[i][j] == 1 else false

end CFSG.Quasithin.B45Mat.Ind
