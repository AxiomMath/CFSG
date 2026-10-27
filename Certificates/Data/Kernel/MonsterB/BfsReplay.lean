module

public import Init

public section

namespace CFSG.KC.Bfs

@[expose] def rStep (E : Nat → Nat → Nat) (i : Nat) (o : Option Nat) (k : Nat) : Option Nat :=
  match o with
  | none => none
  | some m => if E i k < m then some m else if E i k = m then some (m + 1) else none

@[expose] def rRow (E : Nat → Nat → Nat) (ngen i m : Nat) : Option Nat :=
  (List.range ngen).foldl (rStep E i) (some m)

@[expose] def replayLoop (E : Nat → Nat → Nat) (ngen : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, m => some m
  | c + 1, i, m =>
    if i < m then
      match rRow E ngen i m with
      | none => none
      | some m' => replayLoop E ngen c (i + 1) m'
    else none

@[expose] def replayOK (E : Nat → Nat → Nat) (ngen n : Nat) : Bool :=
  replayLoop E ngen n 0 1 == some n

end CFSG.KC.Bfs
