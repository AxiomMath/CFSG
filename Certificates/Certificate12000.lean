module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GH74.Uniqueness.SU.K

private theorem gl23_eq_neg_one_of_central (g : GL (Fin 2) (ZMod 3))
    (hc : ∀ h : GL (Fin 2) (ZMod 3), h * g = g * h) (h1 : g ≠ 1) : g = -1 := by
  revert g
  decide +kernel

end CFSG.GH74.Uniqueness.SU.K

namespace Certificates

theorem certificate12000 :
    ∀ (g : GL (Fin 2) (ZMod 3)), (∀ h : GL (Fin 2) (ZMod 3), h * g = g * h) → g ≠ 1 → g = -1 :=
  CFSG.GH74.Uniqueness.SU.K.gl23_eq_neg_one_of_central

end Certificates
