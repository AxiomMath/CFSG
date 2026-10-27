module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.Z4c2

open Matrix

theorem inverting_of_mul_eq {K : Type} [Field K] (g w : SpecialLinearGroup (Fin 2) K)
    (h : (w : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) =
      Matrix.adjugate (g : Matrix (Fin 2) (Fin 2) K) * (w : Matrix (Fin 2) (Fin 2) K)) :
    w * g * w⁻¹ = g⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  simpa using h

theorem exists_inverting_sl2 {K : Type} [Field K] [CharP K 2]
    (g : SpecialLinearGroup (Fin 2) K) :
    ∃ w : SpecialLinearGroup (Fin 2) K, w * g * w⁻¹ = g⁻¹ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨A, hA⟩ := g
  have hdet := hA
  rw [Matrix.det_fin_two] at hdet
  have hAeta : A = !![A 0 0, A 0 1; A 1 0, A 1 1] := Matrix.eta_fin_two A
  set a := A 0 0 with ha
  set b := A 0 1 with hb
  set c := A 1 0 with hc
  set d := A 1 1 with hd
  by_cases hc0 : c ≠ 0
  · set e := (a ^ 2 + 1) / c with he_def
    have he : e * c = a ^ 2 + 1 := by rw [he_def]; field_simp
    have hw : (!![a, e; c, a] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      linear_combination (-1 : K) * he + (-1 : K) * h2
    refine ⟨⟨_, hw⟩, inverting_of_mul_eq _ _ ?_⟩
    simp only [hAeta]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination he + a ^ 2 * h2 - hdet
    · simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (a * b) * h2
    · simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (a * c) * h2
    · simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination he + hdet + (b * c + 1) * h2
  · push Not at hc0
    by_cases hb0 : b ≠ 0
    · set f := (d ^ 2 + 1) / b with hf_def
      have hf : f * b = d ^ 2 + 1 := by rw [hf_def]; field_simp
      have hw : (!![d, b; f, d] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
        rw [Matrix.det_fin_two]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
        linear_combination (-1 : K) * hf + (-1 : K) * h2
      refine ⟨⟨_, hw⟩, inverting_of_mul_eq _ _ ?_⟩
      simp only [hAeta]
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination hf + hdet + (b * c + 1) * h2
      · simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination (b * d) * h2
      · simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination (c * d) * h2
      · simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination hf + d ^ 2 * h2 - hdet
    · push Not at hb0
      have hw : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
        rw [Matrix.det_fin_two]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
        linear_combination (-1 : K) * h2
      refine ⟨⟨_, hw⟩, inverting_of_mul_eq _ _ ?_⟩
      simp only [hAeta]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hb0, hc0]

end CFSG.Quasithin.Z4c2
