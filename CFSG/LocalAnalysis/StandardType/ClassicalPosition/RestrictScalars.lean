module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.StandardType.ClassicalPosition

theorem even_finrank_restrictScalars {K A V : Type} [Field K] [Field A] [Algebra K A]
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower K A V]
    (hA : Even (Module.finrank K A)) (W : Submodule A V) :
    Even (Module.finrank K (W.restrictScalars K)) := by
  have h : Module.finrank K A * Module.finrank A W = Module.finrank K W :=
    Module.finrank_mul_finrank K A W
  have h2 : Module.finrank K (W.restrictScalars K) = Module.finrank K W := rfl
  rw [h2, ← h]
  exact hA.mul_right _

end CFSG.StandardType.ClassicalPosition
