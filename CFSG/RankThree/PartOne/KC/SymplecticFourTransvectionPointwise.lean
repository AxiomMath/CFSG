module

public import CFSG.RankThree.PartOne.KC.SymplecticFourTransvectionRadical

public section

namespace CFSG.RankThree.PartOne.KCSymplecticFour

open Matrix

variable {K : Type} [Field K]

theorem shape_of_fix (M : Matrix (Fin 4) (Fin 4) K) (σ : K ≃+* K)
    (hfix : ∀ s t b : K, M * uMat (σ s) (σ t) (σ b) = uMat s t b * M) :
    M 3 0 = 0 ∧ M 3 1 = 0 ∧ M 3 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧
      M 1 1 = M 0 0 ∧ M 2 2 = M 0 0 ∧ M 3 3 = M 0 0 ∧ M 2 3 = M 0 1 ∧ M 1 3 = - M 0 2 := by
  have h1 := hfix 1 0 0
  have h2 := hfix 0 1 0
  have h3 := hfix 0 0 1
  simp only [map_one, map_zero] at h1 h2 h3
  have e1 := Matrix.ext_iff.mpr h1
  have e2 := Matrix.ext_iff.mpr h2
  have e3 := Matrix.ext_iff.mpr h3
  simp [Fin.forall_fin_succ, uMat, Matrix.mul_apply, Fin.sum_univ_four] at e1 e2 e3
  grind

theorem eq_scalar_add_of_fix {M : Matrix (Fin 4) (Fin 4) K} {μ : K} (h2 : (2 : K) ≠ 0)
    (hμ : μ ≠ 0) (hM : Mᵀ * symplecticFourGram K * M = μ • symplecticFourGram K)
    (σ : K ≃+* K) (hfix : ∀ s t b : K, M * uMat (σ s) (σ t) (σ b) = uMat s t b * M) :
    σ = 1 ∧ ∃ a d : K, a ≠ 0 ∧ M = a • 1 + d • symplecticFourE14 K := by
  obtain ⟨h30, h31, h32, h20, h21, h10, h12, h11, h22, h33, h23, h13⟩ := shape_of_fix M σ hfix
  have i03 := gram_conj_apply M 0 3
  have i13 := gram_conj_apply M 1 3
  have i23 := gram_conj_apply M 2 3
  rw [hM] at i03 i13 i23
  simp [symplecticFourGram] at i03 i13 i23
  have hμa : μ = M 0 0 * M 0 0 := by
    rw [i03, h30, h10, h20, h33]
    ring
  have ha : M 0 0 ≠ 0 := by
    intro h0
    apply hμ
    rw [hμa, h0, mul_zero]
  have h01 : M 0 1 = 0 := by
    have : M 0 0 * (2 * M 0 1) = 0 := by
      rw [h31, h21, h33, h11, h23] at i13
      linear_combination -i13
    exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)).resolve_left h2
  have h02 : M 0 2 = 0 := by
    have : M 0 0 * (2 * M 0 2) = 0 := by
      rw [h32, h12, h33, h22, h13] at i23
      linear_combination -i23
    exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)).resolve_left h2
  have hσ : σ = 1 := by
    ext t
    have e := Matrix.ext_iff.mpr (hfix 0 t 0) 0 1
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_four] at e
    have h : M 0 0 * (σ t - t) = 0 := by linear_combination -e + t * h11
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ha)
  refine ⟨hσ, M 0 0, M 0 3, ha, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticFourE14, h30, h31, h32, h20, h21, h10, h12, h11, h22, h33,
      h01, h02, h23, h13]

end CFSG.RankThree.PartOne.KCSymplecticFour
