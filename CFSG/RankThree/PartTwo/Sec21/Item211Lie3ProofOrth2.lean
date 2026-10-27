module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Lie3Proof

open Matrix

variable {K : Type*} [Field K]

theorem det_eq_one_or_neg_one_of_orth {Y P : Matrix (Fin 2) (Fin 2) K} (hP : P.det ≠ 0)
    (hY : Y * P * Yᵀ = P) : Y.det = 1 ∨ Y.det = -1 := by
  have h := congrArg Matrix.det hY
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have h1 : (Y.det - 1) * (Y.det + 1) * P.det = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · left
      linear_combination h4
    · right
      linear_combination h4
  · exact absurd h3 hP

theorem mul_eq_det_smul_mul_adjugate_transpose {Y P : Matrix (Fin 2) (Fin 2) K}
    (hY : Y * P * Yᵀ = P) : Y.det • (Y * P) = P * (adjugate Y)ᵀ := by
  have h1 : Yᵀ * adjugate Yᵀ = Y.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [mul_adjugate, det_transpose]
  calc Y.det • (Y * P) = Y * P * (Y.det • (1 : Matrix (Fin 2) (Fin 2) K)) := by
        rw [Matrix.mul_smul, Matrix.mul_one]
    _ = Y * P * (Yᵀ * adjugate Yᵀ) := by rw [h1]
    _ = (Y * P * Yᵀ) * adjugate Yᵀ := by simp only [Matrix.mul_assoc]
    _ = P * (adjugate Y)ᵀ := by rw [hY, adjugate_transpose]

theorem orth_rot_relations {Y P : Matrix (Fin 2) (Fin 2) K} (hPs : Pᵀ = P)
    (hY : Y * P * Yᵀ = P) (hdet : Y.det = 1) :
    (Y 0 0 - Y 1 1) * P 0 0 + 2 * Y 0 1 * P 0 1 = 0 ∧
      (Y 0 0 - Y 1 1) * P 1 1 - 2 * Y 1 0 * P 0 1 = 0 ∧
      Y 0 1 * P 1 1 + Y 1 0 * P 0 0 = 0 := by
  have h := mul_eq_det_smul_mul_adjugate_transpose hY
  rw [hdet, one_smul] at h
  have hq : P 1 0 = P 0 1 := by
    have := congrFun (congrFun hPs 0) 1
    simpa using this
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, adjugate_fin_two, hq] at e00 e01 e11
  refine ⟨by linear_combination e00, by linear_combination -e11, by linear_combination e01⟩

theorem orth_refl_relations (h2 : (2 : K) ≠ 0) {Y P : Matrix (Fin 2) (Fin 2) K} (hPs : Pᵀ = P)
    (hP : P.det ≠ 0) (hY : Y * P * Yᵀ = P) (hdet : Y.det = -1) :
    Y 0 0 + Y 1 1 = 0 ∧ 2 * Y 0 0 * P 0 1 + Y 0 1 * P 1 1 - Y 1 0 * P 0 0 = 0 := by
  have h := mul_eq_det_smul_mul_adjugate_transpose hY
  rw [hdet, neg_one_smul] at h
  have hq : P 1 0 = P 0 1 := by
    have := congrFun (congrFun hPs 0) 1
    simpa using this
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, adjugate_fin_two, hq] at e00 e01 e10 e11
  have hdetP : P.det = P 0 0 * P 1 1 - P 0 1 * P 0 1 := by
    rw [Matrix.det_fin_two, hq]
  have ht0 : (Y 0 0 + Y 1 1) * P 0 0 = 0 := by linear_combination -e00
  have ht1 : (Y 0 0 + Y 1 1) * P 1 1 = 0 := by linear_combination -e11
  have ht2 : (Y 0 0 + Y 1 1) * P 0 1 = 0 := by
    have : 2 * ((Y 0 0 + Y 1 1) * P 0 1) = 0 := by linear_combination -e01 - e10
    exact (mul_eq_zero.mp this).resolve_left h2
  refine ⟨?_, by linear_combination -e01⟩
  by_contra ht
  apply hP
  rw [hdetP]
  have h0 : P 0 0 = 0 := (mul_eq_zero.mp ht0).resolve_left ht
  have h1 : P 1 1 = 0 := (mul_eq_zero.mp ht1).resolve_left ht
  have h3 : P 0 1 = 0 := (mul_eq_zero.mp ht2).resolve_left ht
  rw [h0, h1, h3]
  ring

theorem orth_mul_comm_or_inv (h2 : (2 : K) ≠ 0) {Y H P : Matrix (Fin 2) (Fin 2) K}
    (hPs : Pᵀ = P) (hP : P.det ≠ 0) (hY : Y * P * Yᵀ = P) (hH : H * P * Hᵀ = P)
    (hH1 : H.det = 1) : Y * H = H * Y ∨ Y * H = adjugate H * Y := by
  have hq : P 1 0 = P 0 1 := by
    have := congrFun (congrFun hPs 0) 1
    simpa using this
  have hdetP : P.det = P 0 0 * P 1 1 - P 0 1 * P 0 1 := by
    rw [Matrix.det_fin_two, hq]
  obtain ⟨g1, g2, g3⟩ := orth_rot_relations hPs hH hH1
  rcases det_eq_one_or_neg_one_of_orth hP hY with hY1 | hY1
  · left
    obtain ⟨f1, f2, f3⟩ := orth_rot_relations hPs hY hY1
    have key : (Y 0 1 * H 1 0 - Y 1 0 * H 0 1 = 0) ∧
        ((Y 0 0 - Y 1 1) * H 0 1 - Y 0 1 * (H 0 0 - H 1 1) = 0) ∧
        ((Y 0 0 - Y 1 1) * H 1 0 - Y 1 0 * (H 0 0 - H 1 1) = 0) := by
      by_cases hp : P 0 0 = 0
      · by_cases hr : P 1 1 = 0
        · have hq0 : P 0 1 ≠ 0 := by
            intro h0
            apply hP
            rw [hdetP, hp, hr, h0]
            ring
          have hb : Y 0 1 = 0 := by
            have : 2 * P 0 1 * Y 0 1 = 0 := by rw [hp] at f1; linear_combination f1
            exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hq0)
          have hc : Y 1 0 = 0 := by
            have : 2 * P 0 1 * Y 1 0 = 0 := by rw [hr] at f2; linear_combination -f2
            exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hq0)
          have hf : H 0 1 = 0 := by
            have : 2 * P 0 1 * H 0 1 = 0 := by rw [hp] at g1; linear_combination g1
            exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hq0)
          have hg : H 1 0 = 0 := by
            have : 2 * P 0 1 * H 1 0 = 0 := by rw [hr] at g2; linear_combination -g2
            exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hq0)
          refine ⟨?_, ?_, ?_⟩ <;> simp [hb, hc, hf, hg]
        ·
          have hD : Y 0 1 * H 1 0 - Y 1 0 * H 0 1 = 0 := by
            have : P 1 1 * (Y 0 1 * H 1 0 - Y 1 0 * H 0 1) = 0 := by
              linear_combination H 1 0 * f3 - Y 1 0 * g3
            exact (mul_eq_zero.mp this).resolve_left hr
          refine ⟨hD, ?_, ?_⟩
          · have : P 1 1 * ((Y 0 0 - Y 1 1) * H 0 1 - Y 0 1 * (H 0 0 - H 1 1)) = 0 := by
              linear_combination H 0 1 * f2 - Y 0 1 * g2 - 2 * P 0 1 * hD
            exact (mul_eq_zero.mp this).resolve_left hr
          · have : P 1 1 * ((Y 0 0 - Y 1 1) * H 1 0 - Y 1 0 * (H 0 0 - H 1 1)) = 0 := by
              linear_combination H 1 0 * f2 - Y 1 0 * g2
            exact (mul_eq_zero.mp this).resolve_left hr
      ·
        have hD : Y 0 1 * H 1 0 - Y 1 0 * H 0 1 = 0 := by
          have : P 0 0 * (Y 0 1 * H 1 0 - Y 1 0 * H 0 1) = 0 := by
            linear_combination -(H 0 1 * f3) + Y 0 1 * g3
          exact (mul_eq_zero.mp this).resolve_left hp
        refine ⟨hD, ?_, ?_⟩
        · have : P 0 0 * ((Y 0 0 - Y 1 1) * H 0 1 - Y 0 1 * (H 0 0 - H 1 1)) = 0 := by
            linear_combination H 0 1 * f1 - Y 0 1 * g1
          exact (mul_eq_zero.mp this).resolve_left hp
        · have : P 0 0 * ((Y 0 0 - Y 1 1) * H 1 0 - Y 1 0 * (H 0 0 - H 1 1)) = 0 := by
            linear_combination H 1 0 * f1 - Y 1 0 * g1 - 2 * P 0 1 * hD
          exact (mul_eq_zero.mp this).resolve_left hp
    obtain ⟨k1, k2, k3⟩ := key
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination k1 | linear_combination k2 | linear_combination -k3 |
        linear_combination -k1
  · right
    obtain ⟨f1, f2⟩ := orth_refl_relations h2 hPs hP hY hY1
    have key : Y 0 0 * (H 0 0 - H 1 1) + Y 0 1 * H 1 0 + Y 1 0 * H 0 1 = 0 := by
      by_cases hp : P 0 0 = 0
      · by_cases hr : P 1 1 = 0
        · have hq0 : P 0 1 ≠ 0 := by
            intro h0
            apply hP
            rw [hdetP, hp, hr, h0]
            ring
          have ha : Y 0 0 = 0 := by
            have : 2 * P 0 1 * Y 0 0 = 0 := by rw [hp, hr] at f2; linear_combination f2
            exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hq0)
          have hf : H 0 1 = 0 := by
            have : 2 * P 0 1 * H 0 1 = 0 := by rw [hp] at g1; linear_combination g1
            exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hq0)
          have hg : H 1 0 = 0 := by
            have : 2 * P 0 1 * H 1 0 = 0 := by rw [hr] at g2; linear_combination -g2
            exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hq0)
          simp [ha, hf, hg]
        · have : P 1 1 * (Y 0 0 * (H 0 0 - H 1 1) + Y 0 1 * H 1 0 + Y 1 0 * H 0 1) = 0 := by
            linear_combination Y 0 0 * g2 + H 1 0 * f2 + Y 1 0 * g3
          exact (mul_eq_zero.mp this).resolve_left hr
      · have : P 0 0 * (Y 0 0 * (H 0 0 - H 1 1) + Y 0 1 * H 1 0 + Y 1 0 * H 0 1) = 0 := by
          linear_combination Y 0 0 * g1 - H 0 1 * f2 + Y 0 1 * g3
        exact (mul_eq_zero.mp this).resolve_left hp
    have hd : Y 1 1 = -Y 0 0 := by linear_combination f1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, adjugate_fin_two, hd] <;>
      first | linear_combination key | linear_combination -key | ring

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
