module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityPairLeaves
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

public section

namespace CFSG.RankThree.PartTwo.Sec19.NF5Pair
open Matrix
open scoped MatrixGroups

@[expose] def PairProp (M : Type*) [Group M] : Prop :=
  ∀ z : M, z ^ 3 = 1 → z ≠ 1 →
    ∃ m : M, (m * z * m⁻¹) * z = z * (m * z * m⁻¹) ∧ m * z * m⁻¹ ∉ Subgroup.zpowers z

variable {F : Type*} [Field F]

theorem mk_eq_iff (g₁ g₂ : GL (Fin 3) F) :
    ProjGenLinGroup.mk g₁ = ProjGenLinGroup.mk g₂ ↔
      ∃ s : F, s ≠ 0 ∧ (g₂ : Matrix (Fin 3) (Fin 3) F) = s • (g₁ : Matrix (Fin 3) (Fin 3) F) := by
  rw [ProjGenLinGroup.mk_eq_mk_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, u.ne_zero, ?_⟩
    rw [← hu, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  · rintro ⟨s, hs, h⟩
    refine ⟨Units.mk0 s hs, ?_⟩
    apply Units.ext
    rw [h, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    rfl

theorem pgl_pow_three {g : GL (Fin 3) F} (h : ProjGenLinGroup.mk g ^ 3 = 1) :
    ∃ c : F, (g : Matrix (Fin 3) (Fin 3) F) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have h1 : ProjGenLinGroup.mk (g ^ 3) = ProjGenLinGroup.mk 1 := by rw [map_pow, h, map_one]
  obtain ⟨s, hs0, hs⟩ := (mk_eq_iff _ _).1 h1
  refine ⟨s⁻¹, ?_⟩
  rw [Units.val_pow_eq_pow_val] at hs
  have h2 : (1 : Matrix (Fin 3) (Fin 3) F) = s • (g : Matrix (Fin 3) (Fin 3) F) ^ 3 := by
    simpa using hs
  calc (g : Matrix (Fin 3) (Fin 3) F) ^ 3 = s⁻¹ • (s • (g : Matrix (Fin 3) (Fin 3) F) ^ 3) := by
        rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    _ = s⁻¹ • 1 := by rw [← h2]

theorem pgl_not_scalar {g : GL (Fin 3) F} (h : ProjGenLinGroup.mk g ≠ 1) (μ : F) :
    (g : Matrix (Fin 3) (Fin 3) F) ≠ μ • (1 : Matrix (Fin 3) (Fin 3) F) := by
  intro hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have h0 : (g : Matrix (Fin 3) (Fin 3) F) = 0 := by simpa using hμ
    have := g.isUnit
    rw [h0] at this
    exact (not_isUnit_zero (M₀ := Matrix (Fin 3) (Fin 3) F)) this
  apply h
  rw [← map_one ProjGenLinGroup.mk]
  refine (mk_eq_iff _ _).2 ⟨μ⁻¹, inv_ne_zero hμ0, ?_⟩
  rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  rfl

section Cases

variable [Finite F]

instance instFinitePGL : Finite PGL(3, F) :=
  Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) F → PGL(3, F))
    ProjGenLinGroup.mk_surjective

theorem mem_zpowers_conj_iff {G : Type*} [Group G] (c a b : G) :
    c * a * c⁻¹ ∈ Subgroup.zpowers (c * b * c⁻¹) ↔ a ∈ Subgroup.zpowers b := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [conj_zpow] at hk
    exact ⟨k, mul_left_cancel (mul_right_cancel hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [conj_zpow]⟩

end Cases

end CFSG.RankThree.PartTwo.Sec19.NF5Pair