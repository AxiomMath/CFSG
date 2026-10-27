module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Higman

variable {K : Type} [Field K] [CharP K 2]

theorem entries_of_cube (a b c e : K) (hdet : a * e - b * c = 1)
    (h3 : (!![a, b; c, e] : Matrix (Fin 2) (Fin 2) K) * !![a, b; c, e] * !![a, b; c, e] = 1) :
    a * e + b * c = 1 ∧ a ^ 3 + b * c * e = 1 ∧ b * (a ^ 2 + a * e + e ^ 2 + b * c) = 0 ∧
      c * (a ^ 2 + a * e + e ^ 2 + b * c) = 0 ∧ a * b * c + e ^ 3 = 1 := by
  have h00 := congrFun (congrFun h3 0) 0
  have h01 := congrFun (congrFun h3 0) 1
  have h10 := congrFun (congrFun h3 1) 0
  have h11 := congrFun (congrFun h3 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination hdet + (b * c) * h2
  · linear_combination h00 - (a * b * c) * h2
  · linear_combination h01
  · linear_combination h10
  · linear_combination h11 - (b * c * e) * h2

theorem trace_eq_one_of_cube (a b c e : K) (hdet : a * e - b * c = 1)
    (h3 : (!![a, b; c, e] : Matrix (Fin 2) (Fin 2) K) * !![a, b; c, e] * !![a, b; c, e] = 1)
    (hne : ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ e = 1)) : a + e = 1 := by
  obtain ⟨h1, h2', h3', h4, h5⟩ := entries_of_cube a b c e hdet h3
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_contra ht
  have hu : a + e + 1 ≠ 0 := by
    intro h
    apply ht
    linear_combination h - h2
  have hs : a ^ 2 + a * e + e ^ 2 + b * c = (a + e + 1) ^ 2 := by
    linear_combination h1 - (a * e + a + e) * h2
  have hs0 : a ^ 2 + a * e + e ^ 2 + b * c ≠ 0 := by
    rw [hs]; exact pow_ne_zero 2 hu
  have hb : b = 0 := (mul_eq_zero.1 h3').resolve_right hs0
  have hc : c = 0 := (mul_eq_zero.1 h4).resolve_right hs0
  subst hb hc
  have hae : a * e = 1 := by linear_combination h1
  have ha3 : a ^ 3 = 1 := by linear_combination h2'
  have hfac : (a + 1) * (a ^ 2 + a + 1) = 0 := by
    linear_combination ha3 + (a ^ 2 + a + 1) * h2
  rcases mul_eq_zero.1 hfac with h | h
  · have ha1 : a = 1 := by linear_combination h - h2
    have he1 : e = 1 := by
      rw [ha1] at hae
      linear_combination hae
    exact hne ⟨ha1, rfl, rfl, he1⟩
  · have ha0 : a ≠ 0 := fun h0 => by rw [h0] at hae; simp at hae
    have : a * (a + e) = a * 1 := by
      linear_combination h + hae - a * h2
    exact ht (mul_left_cancel₀ ha0 this)

section Eigen

variable {k : Type} [Field k] [CharP k 2]

theorem factor_zero (M : Matrix (Fin 2) (Fin 2) k) (hM : M * M = M + 1) {l : k}
    (hl : l ^ 2 + l + 1 = 0) :
    (M - l • (1 : Matrix (Fin 2) (Fin 2) k)) *
      (M - (l + 1) • (1 : Matrix (Fin 2) (Fin 2) k)) = 0 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hM]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul]
  have h3 : l * (l + 1) = 1 := by linear_combination hl - h2
  have h3' : (l + 1) * l = 1 := by rw [mul_comm]; exact h3
  rw [h3', one_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  linear_combination ((1 : Matrix (Fin 2) (Fin 2) k) i j - l * M i j) * h2

theorem exists_eigenvector (M : Matrix (Fin 2) (Fin 2) k) (hM : M * M = M + 1) {l : k}
    (hl : l ^ 2 + l + 1 = 0)
    (hns : ∀ c : k, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) k)) :
    ∃ v : Fin 2 → k, v ≠ 0 ∧ M *ᵥ v = l • v := by
  by_contra hno
  push Not at hno
  have hfz := factor_zero M hM hl
  have hall : ∀ v, M *ᵥ v = (l + 1) • v := by
    intro v
    by_contra hne
    have hw0 : (M - (l + 1) • (1 : Matrix (Fin 2) (Fin 2) k)) *ᵥ v ≠ 0 := by
      intro h
      apply hne
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
      exact h
    have h0 : (M - l • (1 : Matrix (Fin 2) (Fin 2) k)) *ᵥ
        ((M - (l + 1) • (1 : Matrix (Fin 2) (Fin 2) k)) *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, hfz, Matrix.zero_mulVec]
    apply hno _ hw0
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0
  apply hns (l + 1)
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Pi.single_apply, Matrix.one_apply] using this

end Eigen

section SL2

theorem sl2_sq_eq (d : SL(2, K)) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    (d : Matrix (Fin 2) (Fin 2) K) * (d : Matrix (Fin 2) (Fin 2) K) =
      (d : Matrix (Fin 2) (Fin 2) K) + 1 := by
  have hdet := d.2
  rw [Matrix.det_fin_two] at hdet
  have h3 : ((d ^ 3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [hd3]; rfl
  rw [pow_succ, pow_two, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul] at h3
  have hD : (d : Matrix (Fin 2) (Fin 2) K) = !![(d : Matrix (Fin 2) (Fin 2) K) 0 0,
      (d : Matrix (Fin 2) (Fin 2) K) 0 1; (d : Matrix (Fin 2) (Fin 2) K) 1 0,
      (d : Matrix (Fin 2) (Fin 2) K) 1 1] := Matrix.eta_fin_two _
  set a := (d : Matrix (Fin 2) (Fin 2) K) 0 0
  set b := (d : Matrix (Fin 2) (Fin 2) K) 0 1
  set c := (d : Matrix (Fin 2) (Fin 2) K) 1 0
  set e := (d : Matrix (Fin 2) (Fin 2) K) 1 1
  rw [hD] at h3 ⊢
  have hne : ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ e = 1) := by
    rintro ⟨ha, hb, hc, he⟩
    apply hd1
    apply Subtype.ext
    rw [hD, ha, hb, hc, he]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have ht := trace_eq_one_of_cube a b c e hdet h3 hne
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination a * ht - hdet - h2
  · linear_combination b * ht
  · linear_combination c * ht
  · linear_combination e * ht - hdet - h2

theorem sl2_ne_scalar (d : SL(2, K)) (hd1 : d ≠ 1) (c : K) :
    (d : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro h
  have hdet := d.2
  rw [h, Matrix.det_smul, Matrix.det_one] at hdet
  simp only [Fintype.card_fin, mul_one] at hdet
  have hc : c = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (c + 1) ^ 2 = 0 := by linear_combination hdet + (c + 1) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linear_combination this - h2
  apply hd1
  apply Subtype.ext
  rw [h, hc, one_smul]
  rfl

end SL2

end CFSG.LocalAnalysis.UniquenessCase.UCK.Higman
