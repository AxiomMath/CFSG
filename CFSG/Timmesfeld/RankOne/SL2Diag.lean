module

public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.Timmesfeld.RankOne

open CFSG.Timmesfeld.ARS.NaturalModule

variable {K : Type*} [Field K]

theorem exists_eq_diagElt_of_conj_mem_unipotent
    (M : Matrix.SpecialLinearGroup (Fin 2) K)
    (hU : M * upperElt K 1 * M⁻¹ ∈ upperUnipotent K)
    (hL : M * lowerElt K 1 * M⁻¹ ∈ lowerUnipotent K) :
    ∃ μ : Kˣ, M = diagElt μ := by
  obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff K).1 hU
  obtain ⟨s, hs⟩ := (mem_lowerUnipotent_iff K).1 hL
  have hc : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have h1 : (((M * upperElt K 1 * M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) 1 0 =
        -((M : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp [upperElt, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [ht] at h1
    have h2 : -((M : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 = 0 := by
      simpa [upperElt] using h1
    have h3 : ((M : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 = 0 := neg_eq_zero.mp h2
    exact mul_self_eq_zero.mp (by simpa [pow_two] using h3)
  have hb : (M : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have h1 : (((M * lowerElt K 1 * M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) 0 1 =
        -((M : Matrix (Fin 2) (Fin 2) K) 0 1) ^ 2 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp [lowerElt, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [hs] at h1
    have h2 : -((M : Matrix (Fin 2) (Fin 2) K) 0 1) ^ 2 = 0 := by
      simpa [lowerElt] using h1
    have h3 : ((M : Matrix (Fin 2) (Fin 2) K) 0 1) ^ 2 = 0 := neg_eq_zero.mp h2
    exact mul_self_eq_zero.mp (by simpa [pow_two] using h3)
  have hdet := M.2
  rw [Matrix.det_fin_two, hb, hc, mul_zero, sub_zero] at hdet
  have ha : (M : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ ha, ?_⟩
  apply Subtype.ext
  rw [coe_diagElt]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Units.val_mk0]
  · simpa using hb
  · simpa using hc
  · simp only [Units.val_mk0, Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right hdet

end CFSG.Timmesfeld.RankOne
