module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace CFSG.KC.RootOrbit

def rowsOf {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : List (List ℤ) :=
  (List.finRange n).map fun i => (List.finRange n).map fun j => M i j

def rowsZ (r : List (List ℕ)) : List (List ℤ) := r.map fun row => row.map fun a => 2 - (a : ℤ)

def dotL (r x : List ℤ) : ℤ := (List.zipWith (· * ·) r x).sum

def reflL (rows : List (List ℤ)) (i : ℕ) (x : List ℤ) : List ℤ :=
  x.modify i fun a => a - dotL (rows.getD i []) x

def negL (x : List ℤ) : List ℤ := x.map fun a => -a

def unitL (n i : ℕ) : List ℤ := (List.range n).map fun j => if j = i then 1 else 0

def keyL (x : List ℤ) : ℕ := x.foldr (fun a acc => acc * 64 + (a + 32).toNat) 0

def memL (y : List ℤ) (R : List (List ℤ)) : Bool := R.any fun z => keyL z == keyL y && z == y

def signedL (P : List (List ℕ)) : List (List ℤ) :=
  P.map (List.map Int.ofNat) ++ (P.map (List.map Int.ofNat)).map negL

def witAt (rows : List (List ℤ)) (n : ℕ) (R : List (List ℤ)) (W : List (ℕ × ℕ × ℕ)) (k : ℕ) :
    Bool :=
  let w := W.getD k (0, 0, 0)
  decide (w.2.2 < n) && decide (w.1 ≤ 30) &&
    if w.1 = 0 then R.getD k [] == unitL n w.2.2
    else (W.getD w.2.1 (0, 0, 0)).1 + 1 == w.1 && decide (w.2.1 < R.length) &&
      R.getD k [] == reflL rows w.2.2 (R.getD w.2.1 [])

def rootCertB (rows : List (List ℤ)) (n : ℕ) (P : List (List ℕ)) (W : List (ℕ × ℕ × ℕ))
    (N : ℕ) : Bool :=
  (signedL P).length == N && (signedL P).all (fun x => x.length == n) &&
    decide (P.map (List.map Int.ofNat)).Nodup &&
    (P.map (List.map Int.ofNat)).all (fun x => decide (0 < x.sum)) &&
    (List.range n).all (fun i => memL (unitL n i) (signedL P)) &&
    (P.map (List.map Int.ofNat)).all (fun x =>
      (List.range n).all fun i => memL (reflL rows i x) (signedL P)) &&
    (List.range (signedL P).length).all (witAt rows n (signedL P) W)

def foldMv (rows : List (List ℤ)) (a b c : ℕ) (x : List ℤ) : List ℤ :=
  if c = 0 then reflL rows a (reflL rows b x) else reflL rows (c - 1) x

def foldAt (rows : List (List ℤ)) (n a b : ℕ) (R : List (List ℤ)) (F : List (ℕ × ℕ × ℕ))
    (k : ℕ) : Bool :=
  let w := F.getD k (0, 0, 0)
  decide (w.1 ≤ 30) &&
    if w.1 = 0 then decide (w.2.2 < n) && R.getD k [] == unitL n w.2.2
    else (F.getD w.2.1 (0, 0, 0)).1 + 1 == w.1 && decide (w.2.1 < R.length) &&
      (w.2.2 == 0 || decide (w.2.2 - 1 < n) && w.2.2 - 1 != a && w.2.2 - 1 != b) &&
      R.getD k [] == foldMv rows a b w.2.2 (R.getD w.2.1 [])

def foldCertB (rows : List (List ℤ)) (n a b : ℕ) (R : List (List ℤ)) (F : List (ℕ × ℕ × ℕ)) :
    Bool :=
  (List.range R.length).all (foldAt rows n a b R F)

end CFSG.KC.RootOrbit
