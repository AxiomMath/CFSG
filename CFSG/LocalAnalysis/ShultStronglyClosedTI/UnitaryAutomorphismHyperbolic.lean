module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneNormalizer

public section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_semilinear_hypPSU (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (α : MulAut (hypPSU h 1 1)) :
    ∃ x : semilinearSimilitudes h 1 1, ∀ g : hypSU h 1 1,
      α (hypProj h 1 1 g) = hypProj h 1 1 ⟨_, conj_mem_hypSU x.2 g⟩ := by
  have hmem : linePerm h le_rfl le_rfl α ∈ semilinearPointGroup h 1 1 := by
    rw [← (unitary_rank_one_permutation_normalizer h hq).1, ← range_linePerm h le_rfl le_rfl]
    exact ⟨α, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, fun g => hypProjLineAction_injective h (by norm_num) ?_⟩
  rw [← linePerm_conj h le_rfl le_rfl, ← hx, semilinearPointAction_conj]

theorem scalar_mul_conj_eq {ι : Type} [Fintype ι] [DecidableEq ι] (c : Kˣ) (B : GL ι K)
    (σ : K ≃+* K) (g : GL ι K) :
    GeneralLinearGroup.scalar ι c * B * glAut σ g * (GeneralLinearGroup.scalar ι c * B)⁻¹ =
      B * glAut σ g * B⁻¹ := by
  have hc := (commute_scalar c (B * glAut σ g * B⁻¹)).eq
  calc GeneralLinearGroup.scalar ι c * B * glAut σ g * (GeneralLinearGroup.scalar ι c * B)⁻¹
      = GeneralLinearGroup.scalar ι c * (B * glAut σ g * B⁻¹) *
          (GeneralLinearGroup.scalar ι c)⁻¹ := by group
    _ = B * glAut σ g * B⁻¹ := by rw [← hc, mul_inv_cancel_right]

theorem scalar_mul_isometry {ι : Type} [Fintype ι] [DecidableEq ι] (h : UnitaryFieldData p f K)
    {G : Matrix ι ι K} {B : GL ι K} {μ : K}
    (hB : ((B : Matrix ι ι K).map h.bar)ᵀ * G * (B : Matrix ι ι K) = μ • G) {c : Kˣ}
    (hc : h.norm (c : K) * μ = 1) :
    (((GeneralLinearGroup.scalar ι c * B : GL ι K) : Matrix ι ι K).map h.bar)ᵀ * G *
      ((GeneralLinearGroup.scalar ι c * B : GL ι K) : Matrix ι ι K) = G := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal,
    Matrix.smul_mul, Matrix.one_mul, Matrix.map_smul' _ _ _ (map_mul h.bar), transpose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [hB, smul_smul, smul_smul, ← UnitaryFieldData.norm, hc, one_smul]

theorem exists_isometry_hypPSU (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (α : MulAut (hypPSU h 1 1)) :
    ∃ (σ : K ≃+* K) (B : GL (HypIndex 1 1) K),
      ((B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar)ᵀ * hypGram 1 1 K *
          (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = hypGram 1 1 K ∧
        ∀ g : hypSU h 1 1, ∃ hg : B * glAut σ (g : GL (HypIndex 1 1) K) * B⁻¹ ∈ hypSU h 1 1,
          α (hypProj h 1 1 g) = hypProj h 1 1 ⟨_, hg⟩ := by
  obtain ⟨x, hx⟩ := exists_semilinear_hypPSU h hq α
  obtain ⟨μ, hμ0, hμ, hB⟩ := mem_semilinearSimilitudes.mp x.2
  obtain ⟨c, hc⟩ := h.normHom_surjective ⟨μ⁻¹, by
    rw [UnitaryFieldData.mem_fixedField, map_inv₀, hμ]⟩
  have hc' : h.norm c = μ⁻¹ := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at hc'
    exact inv_ne_zero hμ0 hc'.symm
  refine ⟨(x : SemiGL (HypIndex 1 1) K).right,
    GeneralLinearGroup.scalar _ (Units.mk0 c hc0) * (x : SemiGL (HypIndex 1 1) K).left,
    scalar_mul_isometry h hB (by rw [Units.val_mk0, hc', inv_mul_cancel₀ hμ0]), fun g => ?_⟩
  rw [scalar_mul_conj_eq]
  exact ⟨conj_mem_hypSU x.2 g, hx g⟩

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
