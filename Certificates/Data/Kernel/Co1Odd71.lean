module

public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1Odd71Data

public section

namespace CFSG.KD.Co1Odd

open CFSG.KC.Co1F2 CFSG.KC.M1F2

@[expose] noncomputable def ptOK71 (G P par lab : List Nat) (i : Nat) : Bool :=
  i == 0 || (decide (par.getD i 0 < i) && decide (lab.getD i 0 < G.length) &&
    P.getD i 0 == mulF 24 (P.getD (par.getD i 0) 0) (G.getD (lab.getD i 0) 0))

@[expose] noncomputable def ptsOK71 (G P par lab : List Nat) (lo cnt : Nat) : Bool :=
  (List.range' lo cnt).all (ptOK71 G P par lab)

@[expose] noncomputable def treeOK71 (G P par lab : List Nat) (n : Nat) : Bool :=
  P.length == n && par.length == n && lab.length == n && P.getD 0 0 == idF 24 &&
    ptsOK71 G P par lab 0 n

@[expose] def distinctL : List Nat → Bool
  | [] => true
  | a :: t => !t.contains a && distinctL t

@[expose] noncomputable def canonB (M : Nat) : Bool :=
  M == CFSG.KLie.CT.orN 24 fun i => rowF 24 M i <<< (24 * i)

@[expose] noncomputable def canonsL (L : List Nat) (lo cnt : Nat) : Bool :=
  (List.range' lo cnt).all fun i => canonB (L.getD i 0)

@[expose] noncomputable def canonL (L : List Nat) : Bool := canonsL L 0 L.length

@[expose] noncomputable def invK (M : Nat) : Bool := mulF 24 M M == idF 24

@[expose] noncomputable def rankOK (M : Nat) (W : List Nat) : Bool :=
  W.length == 9 && pivK 24 (W.map fun v => vmF 24 (trK 24 M) v ^^^ v) 0

@[expose] noncomputable def ncOK71 (P : List Nat) (W : List (List Nat)) (i : Nat) : Bool :=
  P.getD i 0 == idF 24 || !invK (P.getD i 0) || rankOK (P.getD i 0) (W.getD i [])

@[expose] noncomputable def ncsOK71 (P : List Nat) (W : List (List Nat)) (lo cnt : Nat) : Bool :=
  (List.range' lo cnt).all (ncOK71 P W)

@[expose] noncomputable def noConjOK (P : List Nat) (W : List (List Nat)) : Bool :=
  ncsOK71 P W 0 P.length

theorem all_range'_add (f : Nat → Bool) (lo a b : Nat) :
    (List.range' lo (a + b)).all f = ((List.range' lo a).all f && (List.range' (lo + a) b).all f) := by
  rw [← List.range'_append, List.all_append, Nat.one_mul]

end CFSG.KD.Co1Odd

end
