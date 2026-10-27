module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerDefs

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal
open Matrix TauCeti
open CFSG.ComponentClassification.CatalogueBHigherLinearField

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

theorem exists_sq_factor_units {F : Type} [Field F] [Finite F] [CharP F 2] (μ : Fˣ) :
    ∃ γ : Fˣ, γ * γ = μ := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (μ : F)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact Units.ne_zero μ (by simpa using hr)
  refine ⟨Units.mk0 r hr0, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mk0]
  exact hr.symm

theorem exists_isometry_of_linear_similitude {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {Q : QuadraticForm F (ι → F)} {A : GL ι F} {μ : Fˣ}
    (h : ∀ v, Q (A.val *ᵥ v) = (μ : F) * Q v) :
    ∃ γ : Fˣ, ∃ A' : GL ι F, (A'.val = (γ : F)⁻¹ • A.val) ∧
      ∀ v, Q (A'.val *ᵥ v) = Q v := by
  obtain ⟨γ, hγ⟩ := exists_sq_factor_units μ
  let A' : GL ι F := GeneralLinearGroup.scalar ι γ⁻¹ * A
  have hA' : A'.val = (γ : F)⁻¹ • A.val := by
    change (↑(GeneralLinearGroup.scalar ι γ⁻¹ * A) : Matrix ι ι F) = (γ : F)⁻¹ • A.val
    have hsc : (Matrix.scalar ι (↑(γ⁻¹)) : Matrix ι ι F) =
        (γ : F)⁻¹ • (1 : Matrix ι ι F) := by
      rw [Units.val_inv_eq_inv_val]
      exact (smul_one_eq_diagonal _).symm
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hsc, Matrix.smul_mul, one_mul]
  refine ⟨γ, A', hA', ?_⟩
  intro v
  have hγμ : (μ : F) = (γ : F) * (γ : F) := by
    rw [← Units.val_mul, hγ]
  have hγ0 : (γ : F) ≠ 0 := Units.ne_zero γ
  have hscalar : (γ : F)⁻¹ * (γ : F)⁻¹ * ((γ : F) * (γ : F)) = 1 := by
    field_simp
  calc
    Q (A'.val *ᵥ v) = Q ((γ : F)⁻¹ • (A.val *ᵥ v)) := by rw [hA', Matrix.smul_mulVec]
    _ = ((γ : F)⁻¹ * (γ : F)⁻¹) * Q (A.val *ᵥ v) := by
          rw [QuadraticMap.map_smul, smul_eq_mul]
    _ = ((γ : F)⁻¹ * (γ : F)⁻¹) * ((μ : F) * Q v) := by rw [h v]
    _ = Q v := by
          rw [hγμ, ← mul_assoc, hscalar, one_mul]

theorem matrixAction_field_eq_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {Q : QuadraticForm F (ι → F)} {A : GL ι F} {φ : F ≃+* F} {μ : Fˣ}
    {y : MulAut ↥(spinGroup Q)} (hφ : ∀ x : F, φ x = x)
    (hmat : GGMatrixSemilinearAction Q A φ μ y) :
    GGMatrixSemilinearAction Q A (RingEquiv.refl F) μ y := by
  have hφ' : φ = RingEquiv.refl F := RingEquiv.ext hφ
  subst hφ'
  exact hmat

theorem matrixAction_of_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {Q : QuadraticForm F (ι → F)} {A A' : GL ι F} {c : F} (hc : c ≠ 0)
    (hAA' : A.val = c • A'.val) {y : MulAut ↥(spinGroup Q)} :
    GGMatrixSemilinearAction Q A (RingEquiv.refl F) 1 y ↔
      GGMatrixSemilinearAction Q A' (RingEquiv.refl F) 1 y := by
  have hX : (c : F) • (↑(A⁻¹) : Matrix ι ι F) = (↑(A'⁻¹) : Matrix ι ι F) := by
    have hc1 : (c : F) * c⁻¹ = 1 := mul_inv_cancel₀ hc
    have hv : (↑A' : Matrix ι ι F) * (↑(A'⁻¹) : Matrix ι ι F) = 1 := by
      show (↑A' : Matrix ι ι F) * A'.inv = 1
      exact Units.val_inv A'
    have hstep : (↑A : Matrix ι ι F) * ((c : F)⁻¹ • (↑(A'⁻¹) : Matrix ι ι F)) = 1 := by
      rw [hAA', Matrix.smul_mul, Algebra.mul_smul_comm, hv, smul_smul, hc1, one_smul]
    have hstep2 : (↑A : Matrix ι ι F) * (↑(A⁻¹) : Matrix ι ι F) = 1 := by
      show (↑A : Matrix ι ι F) * A.inv = 1
      exact Units.val_inv A
    have heq : (c : F)⁻¹ • (↑(A'⁻¹) : Matrix ι ι F) = (↑(A⁻¹) : Matrix ι ι F) :=
      IsUnit.mul_left_cancel (Units.isUnit A) (hstep.trans hstep2.symm)
    calc (c : F) • (↑(A⁻¹) : Matrix ι ι F)
        = (c : F) • ((c : F)⁻¹ • (↑(A'⁻¹) : Matrix ι ι F)) := by rw [heq]
      _ = ((c : F) * (c : F)⁻¹) • (↑(A'⁻¹) : Matrix ι ι F) := by rw [smul_smul]
      _ = (↑(A'⁻¹) : Matrix ι ι F) := by rw [hc1, one_smul]
  have hconj : ∀ M : Matrix ι ι F,
      (↑A : Matrix ι ι F) * M * (↑(A⁻¹) : Matrix ι ι F) =
        (↑A' : Matrix ι ι F) * M * (↑(A'⁻¹) : Matrix ι ι F) := by
    intro M
    rw [hAA', Matrix.smul_mul, Matrix.smul_mul, mul_assoc, ← Algebra.mul_smul_comm,
        ← Algebra.mul_smul_comm, hX, mul_assoc]
  constructor
  · intro hM x
    apply Units.ext
    rw [hM x]
    simp only [Units.val_mul]
    exact hconj _
  · intro hM x
    apply Units.ext
    rw [hM x]
    simp only [Units.val_mul]
    exact (hconj _).symm

end CFSG.StandardType.LieKnownR2.POmega.Inner
