module

public import Init

public section

namespace CFSG.KC.Bfs

@[expose] def rStepT (E : Nat → Nat → Nat) (P Lb : Nat → Nat) (i : Nat) (o : Option Nat) (k : Nat) :
    Option Nat :=
  match o with
  | none => none
  | some m => if E i k < m then some m
    else if E i k = m ∧ P m = i ∧ Lb m = k then some (m + 1) else none

@[expose] def rRowT (E : Nat → Nat → Nat) (P Lb : Nat → Nat) (ngen i m : Nat) : Option Nat :=
  (List.range ngen).foldl (rStepT E P Lb i) (some m)

@[expose] def replayLoopT (E : Nat → Nat → Nat) (P Lb : Nat → Nat) (ngen : Nat) :
    Nat → Nat → Nat → Option Nat
  | 0, _, m => some m
  | c + 1, i, m =>
    if i < m then
      match rRowT E P Lb ngen i m with
      | none => none
      | some m' => replayLoopT E P Lb ngen c (i + 1) m'
    else none

@[expose] def replayTOK (E : Nat → Nat → Nat) (P Lb : Nat → Nat) (ngen n : Nat) : Bool :=
  replayLoopT E P Lb ngen n 0 1 == some n

end CFSG.KC.Bfs
