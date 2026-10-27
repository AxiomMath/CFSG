module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LargeExtraspecial.DW37Input
public import CFSG.GroupTheory.GLnTwoSplitting.SpecialLinear

public section

open scoped MatrixGroups Matrix

namespace CFSG.ASVolI.ChH.GL

open CFSG.LocalAnalysis.ComponentInitial

@[expose] noncomputable def glEquivSL (n : ℕ) : GL (Fin n) (ZMod 2) ≃* SL(n, ZMod 2) :=
  (MulEquiv.ofBijective (Matrix.SpecialLinearGroup.toGL : SL(n, ZMod 2) →* GL (Fin n) (ZMod 2))
    ⟨Matrix.SpecialLinearGroup.toGL_injective,
      CFSG.GroupTheory.GLnTwoSplitting.toGL_surjective_zmod_two⟩).symm

theorem coe_glEquivSL (n : ℕ) (X : GL (Fin n) (ZMod 2)) :
    ((glEquivSL n X : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = X := by
  have h := congrArg Units.val
    (MulEquiv.apply_symm_apply (MulEquiv.ofBijective
      (Matrix.SpecialLinearGroup.toGL : SL(n, ZMod 2) →* GL (Fin n) (ZMod 2))
      ⟨Matrix.SpecialLinearGroup.toGL_injective,
        CFSG.GroupTheory.GLnTwoSplitting.toGL_surjective_zmod_two⟩) X)
  exact h

theorem proj_injective_zmod_two (n : ℕ) : Function.Injective (LinearFlag.proj n (ZMod 2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, LinearFlag.ker_proj, LinearFlag.scalars_eq_center]
  exact CFSG.LargeExtraspecial.DW.center_specialLinearGroup_zmod_two_eq_bot n

@[expose] noncomputable def glEquivProj (n : ℕ) :
    GL (Fin n) (ZMod 2) ≃* LinearFlag.projectiveSL n (ZMod 2) :=
  (glEquivSL n).trans (MulEquiv.ofBijective (LinearFlag.proj n (ZMod 2))
    ⟨proj_injective_zmod_two n, LinearFlag.proj_surjective n (ZMod 2)⟩)

theorem glEquivProj_apply (n : ℕ) (X : GL (Fin n) (ZMod 2)) :
    glEquivProj n X = LinearFlag.proj n (ZMod 2) (glEquivSL n X) := rfl

theorem glEquivProj_symm_conjAut (n : ℕ) (A X : GL (Fin n) (ZMod 2)) :
    (glEquivProj n).symm (LinearFlag.conjAut n (ZMod 2) A (glEquivProj n X)) = A * X * A⁻¹ := by
  apply (glEquivProj n).injective
  rw [MulEquiv.apply_symm_apply, glEquivProj_apply, LinearFlag.conjAut_proj, glEquivProj_apply]
  congr 1
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, coe_glEquivSL, coe_glEquivSL, Units.val_mul, Units.val_mul]

theorem coe_glEquivProj_symm_conjAut_dualAut (n : ℕ) (A X : GL (Fin n) (ZMod 2)) :
    (((glEquivProj n).symm (LinearFlag.conjAut n (ZMod 2) A
        (LinearFlag.dualAut n (ZMod 2) (glEquivProj n X))) : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
        ((X⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *
          ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  set Y := (glEquivProj n).symm (LinearFlag.conjAut n (ZMod 2) A
    (LinearFlag.dualAut n (ZMod 2) (glEquivProj n X))) with hY
  have h1 : glEquivProj n Y = LinearFlag.conjAut n (ZMod 2) A
      (LinearFlag.dualAut n (ZMod 2) (glEquivProj n X)) := MulEquiv.apply_symm_apply _ _
  rw [glEquivProj_apply, glEquivProj_apply, LinearFlag.dualAut_proj, LinearFlag.conjAut_proj] at h1
  have h2 := proj_injective_zmod_two n h1
  have h3 := congrArg (fun g : SL(n, ZMod 2) => (g : Matrix (Fin n) (Fin n) (ZMod 2))) h2
  simp only [LinearFlag.coe_slConjugation] at h3
  rw [coe_glEquivSL] at h3
  rw [h3]
  have h4 : (glEquivSL n X)⁻¹ = glEquivSL n X⁻¹ := (map_inv (glEquivSL n) X).symm
  rw [Matrix.SpecialLinearGroup.coe_transpose, h4, coe_glEquivSL]

end CFSG.ASVolI.ChH.GL
