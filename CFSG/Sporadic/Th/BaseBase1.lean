
module

public import CFSG.Sporadic.Th.BaseBase

public import CFSG.Sporadic.Th.Plane
public import CFSG.Sporadic.Th.FormBase
public import Certificates.Data.CFSGNative.Th.Base
public meta import Certificates.Data.CFSGNative.Th.Base
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate

@[expose] public section

namespace CFSG.Sporadic.Th

open Native Matrix Pointwise

theorem form_invariant : ∀ g ∈ J,
    ((g : Matrix (Fin 248) (Fin 248) (ZMod 2)))ᵀ * formF * (g : Matrix (Fin 248) (Fin 248) (ZMod 2))
      = formF := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact matA_form
    · exact matB_form
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, Matrix.transpose_mul]
    calc (y.val)ᵀ * (x.val)ᵀ * formF * (x.val * y.val)
        = (y.val)ᵀ * ((x.val)ᵀ * formF * x.val) * y.val := by simp only [Matrix.mul_assoc]
      _ = formF := by rw [hx, hy]
  | inv x _ hx =>
    have h1 : x.val * (x⁻¹ : GL (Fin 248) (ZMod 2)).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((x⁻¹ : GL (Fin 248) (ZMod 2)).val)ᵀ * formF * (x⁻¹ : GL (Fin 248) (ZMod 2)).val
        = ((x⁻¹ : GL (Fin 248) (ZMod 2)).val)ᵀ * ((x.val)ᵀ * formF * x.val) *
            (x⁻¹ : GL (Fin 248) (ZMod 2)).val := by rw [hx]
      _ = (x.val * (x⁻¹ : GL (Fin 248) (ZMod 2)).val)ᵀ * formF *
            (x.val * (x⁻¹ : GL (Fin 248) (ZMod 2)).val) := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = formF := by rw [h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

end CFSG.Sporadic.Th
