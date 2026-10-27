module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Sporadic.LyI301

open Equiv

@[expose] def lyU : Fin 4 → Perm (Fin 11) :=
  ![swap 3 4 * swap 5 9 * (swap 6 7 * swap 8 10), swap 3 5 * swap 4 9 * (swap 6 7 * swap 8 10),
    swap 3 4 * swap 5 9 * (swap 6 8 * swap 7 10), swap 3 4 * swap 5 9 * (swap 6 10 * swap 7 8)]

@[expose] def lyV : List (Perm (Fin 11)) :=
  (List.finRange 16).map fun k =>
    lyU 0 ^ (k.val % 2) * lyU 1 ^ (k.val / 2 % 2) * lyU 2 ^ (k.val / 4 % 2) * lyU 3 ^ (k.val / 8)

@[expose] def lyX1 : Perm (Fin 11) := swap 0 2 * swap 0 1

@[expose] def lyX2 : Perm (Fin 11) := swap 3 5 * swap 3 4

@[expose] def lyX3 : Perm (Fin 11) := swap 6 8 * swap 6 7

@[expose] def lyConj : List (Perm (Fin 11)) := [lyX3, lyX1 * lyX2]

@[expose] def lySplit (σ₃ : Perm {i : Fin 11 // i.val < 3}) (σ₈ : Perm {i : Fin 11 // ¬ i.val < 3}) :
    Perm (Fin 11) :=
  Perm.subtypeCongr σ₃ σ₈

end CFSG.Sporadic.LyI301
