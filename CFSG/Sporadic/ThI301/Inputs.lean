module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Sporadic.ThI301

open Equiv

@[expose] def permT : Perm (Fin 9) := swap 0 7 * swap 0 8 * (swap 1 2 * swap 1 4)

@[expose] def permW1 : Perm (Fin 9) :=
  swap 0 4 * swap 1 7 * swap 2 8 * swap 3 5 * (swap 0 2 * swap 1 8 * swap 3 6 * swap 4 7)

@[expose] def permW2 : Perm (Fin 9) := swap 0 8 * swap 1 2 * permW1 * (swap 0 8 * swap 1 2)⁻¹

@[expose] def a9Conj : List (Perm (Fin 9)) := [permW2, permW1 * permW2, permT * permW2]

end CFSG.Sporadic.ThI301
