module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.Quasithin.Fan86

@[expose] def fcomm {H : Type*} [Group H] (a b : H) : H := a⁻¹ * b⁻¹ * a * b

@[expose] def kstar (i j : Fin 5) : Fin 5 := 2 * j - i

@[expose] def midlab (i j : Fin 5) : Fin 5 := 3 * (i + j)

@[expose] def tauLab (j : Fin 5) : Fin 5 := 2 * j + 3

@[expose] def prodFive {H : Type*} [Group H] (f : Fin 5 → H) : H := f 0 * f 1 * f 2 * f 3 * f 4

end CFSG.Quasithin.Fan86
