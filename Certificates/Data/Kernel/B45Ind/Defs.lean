module

public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.KC.B45Ind

@[expose] def comp24L (a b : List ℕ) : List ℕ :=
  (List.range 24).map fun i => a.getD (b.getD i 0) 0

@[expose] def invL (a : List ℕ) : List ℕ :=
  (List.range 24).foldl (fun b i => b.set (a.getD i 0) i) (List.replicate 24 0)

@[expose] def wordL (a b : List ℕ) : List Bool → List ℕ
  | [] => List.range 24
  | z :: w => comp24L (if z then b else a) (wordL a b w)

@[expose] def piL (ts : List (List ℕ)) (g : List ℕ) (p : ℕ) : List ℕ :=
  let pts := ts.map (·.getD p 0)
  ts.map fun t => (pts.findIdx? (· == (comp24L g t).getD p 0)).getD 0

@[expose] def hL (ts : List (List ℕ)) (g pi : List ℕ) : List (List ℕ) :=
  (List.range ts.length).map fun k =>
    comp24L (comp24L (invL (ts.getD (pi.getD k 0) [])) g) (ts.getD k [])

@[expose] def piOKL (ts : List (List ℕ)) (g : List ℕ) (p : ℕ) (pi : List ℕ) : Bool :=
  (List.range ts.length).all fun k =>
    pi.getD k 0 < ts.length &&
      (ts.getD (pi.getD k 0) []).getD p 0 == (comp24L g (ts.getD k [])).getD p 0

@[expose] def cosetOKL (a b : List ℕ) (ts : List (List ℕ)) (m p : ℕ) : Bool :=
  ts.length == m &&
    ((List.range m).all fun k => (List.range m).all fun k' =>
      k == k' || (ts.getD k []).getD p 0 != (ts.getD k' []).getD p 0) &&
    piOKL ts a p (piL ts a p) && piOKL ts b p (piL ts b p) &&
    (List.range m).all fun k => (List.range 24).all fun j =>
      (invL (ts.getD k [])).getD ((ts.getD k []).getD j 0) 0 == j

@[expose] def indColsL (d : ℕ) (Xc : Array ℕ → ℕ → ℕ) (ts : List (List ℕ)) (g : List ℕ)
    (p : ℕ) : List ℕ :=
  let pi := piL ts g p
  let hs := hL ts g pi
  (List.range (ts.length * d)).map fun j =>
    Xc (hs.getD (j / d) []).toArray (1 <<< (j % d)) <<< (d * pi.getD (j / d) 0)

@[expose] def scanIdx {α : Type} (q : α → Bool) (i : ℕ) : ℕ → List α → Option ℕ
  | _, [] => none
  | k, e :: l => if decide (i ≤ k) && q e then some k else scanIdx q i (k + 1) l

@[expose] def pivL (st : List (ℕ × ℕ)) (i : ℕ) : Option ℕ :=
  scanIdx (fun e => e.1.testBit i) i 0 st

@[expose] def swapL (st : List (ℕ × ℕ)) (i j : ℕ) : List (ℕ × ℕ) :=
  if i < st.length ∧ j < st.length then (st.set i (st.getD j (0, 0))).set j (st.getD i (0, 0))
  else st

@[expose] def mapIdxFrom {α β : Type} (f : ℕ → α → β) : ℕ → List α → List β
  | _, [] => []
  | k, e :: l => f k e :: mapIdxFrom f (k + 1) l

@[expose] def invStepL (st : List (ℕ × ℕ)) (i : ℕ) : List (ℕ × ℕ) :=
  match pivL st i with
  | none => st
  | some j =>
    let st' := swapL st i j
    let piv := st'.getD i (0, 0)
    mapIdxFrom (fun j' e => if j' != i && e.1.testBit i then (e.1 ^^^ piv.1, e.2 ^^^ piv.2) else e)
      0 st'

@[expose] def invColsL (n : ℕ) (P : List ℕ) : List ℕ :=
  let st := (List.range n).map fun j => (P.getD j 0, 1 <<< j)
  ((List.range n).foldl invStepL st).map (·.2)

end CFSG.KC.B45Ind
