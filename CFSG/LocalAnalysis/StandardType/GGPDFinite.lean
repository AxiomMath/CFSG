module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FinCases

public section

open scoped BigOperators

namespace CFSG.StandardType.PDFinite

@[expose] def ggPDF_C3 : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  CartanMatrix.F₄.map (fun z : ℤ => (z : ZMod 3))

@[expose] def ggPDF_refl (i : Fin 4) (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) :
    Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  1 - Matrix.single i i 1 * M

@[expose] def ggPDF_S (i : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod 3) := ggPDF_refl i ggPDF_C3

theorem ggPDF_S_mul_self (i : Fin 4) : ggPDF_S i * ggPDF_S i = 1 := by
  fin_cases i <;> decide +kernel

end CFSG.StandardType.PDFinite

end
