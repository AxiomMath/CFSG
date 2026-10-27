module

public import CFSG.RankThree.Native.ONTripleLocalCheckInputs

public section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.KC.Misc.F7 CFSG.KC.Loop

@[expose] def lineWords : List (List (List ℕ)) :=
  [[[1, 0, 0, 0, 1, 0, 0, 1, 0, 1], [], [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0],
      [0, 1, 0, 0, 0, 1, 0, 1, 0]],
    [[1, 0, 0, 1], [], [0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0], [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0]]]

@[expose] def sYList : List (List ℕ) := [[2, 0, 1, 3, 4, 5], [2, 0, 1, 4, 5, 3]]

@[expose] noncomputable def wordNM (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idM
    (fun k _ ih => mmul (rM ((ifN (Nat.beq k 0) (rN1) (rN2)))) ih) w

@[expose] noncomputable def chkLM : Bool :=
  allN 2 fun j => allN 4 fun l =>
    Nat.beq (rM (nthN (nthLN rL j) l)) (wordNM (lineW j l))
where
  lineW (j l : Nat) : List Nat :=
    List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
      (fun x _ ih k => Nat.rec (motive := fun _ => List Nat) (nthLN x l) (fun k' _ => ih k') k)
      lineWords j

@[expose] noncomputable def chkVx0M : Bool :=
  allN 2 fun j => allN 3 fun m => allL (vRegs j m) fun t =>
    Nat.beq (mmul (rM t) (rM (nthN rX 0))) (mmul (rM (nthN rX 0)) (rM t))

@[expose] noncomputable def chkYM : Bool :=
  (andB (mapsBlocksM (rIM rY1) (nthLN sYList 0) 21) (mapsBlocksM (rIM rY3) (nthLN sYList 1) 22))

@[expose] noncomputable def chkX12M : Bool :=
  Nat.beq (rM rX12) (mmul (rM (nthN rX 1)) (rM (nthN rX 2)))

end CFSG.RankThree.Native.ONTriple

end
