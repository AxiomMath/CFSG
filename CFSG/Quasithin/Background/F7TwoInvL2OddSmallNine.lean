module

public import CFSG.Quasithin.Background.F7TwoInvL2OddSmallAlg
public import CFSG.Quasithin.Background.F7TwoInvL2OddNonsplit

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GorensteinWalter CFSG.PSL2Table
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem exists_data_nine [Finite K] (h9 : Nat.card K = 9) {ν : K} (hν : ¬ IsSquare ν) :
    ∃ i : K, i * i = -1 ∧ ν ^ 4 = -1 ∧ (3 : K) = 0 := by
  let : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card]; exact h9
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2) (by simpa using hcardK)
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hF : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hν0 : ν ≠ 0 := ne_zero_of_not_isSquare hν
  have hhalf : Fintype.card K / 2 = 4 := by rw [hcardK]
  have hν4 : ν ^ 4 = -1 := by
    rcases FiniteField.pow_dichotomy hF hν0 with h | h
    · rw [hhalf] at h
      exact absurd ((FiniteField.isSquare_iff hF hν0).2 (by rwa [hhalf])) hν
    · rwa [hhalf] at h
  obtain ⟨i, hi⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).2 (by rw [hcardK]; norm_num)
  exact ⟨i, hi.symm, hν4, h3⟩

@[expose] def matA9 (i : K) : SL(2, K) := ⟨!![i, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

@[expose] def matA9' (ν i : K) (hν : ν ≠ 0) : SL(2, K) :=
  ⟨!![0, -ν; ν⁻¹, i], by simp [Matrix.det_fin_two_of, hν]⟩

@[simp] theorem coe_matA9 (i : K) :
    (matA9 i : Matrix (Fin 2) (Fin 2) K) = !![i, 1; -1, 0] := rfl

@[simp] theorem coe_matA9' (ν i : K) (hν : ν ≠ 0) :
    (matA9' ν i hν : Matrix (Fin 2) (Fin 2) K) = !![0, -ν; ν⁻¹, i] := rfl

theorem nonsplitJ_mul_matA9 (ν : K) (hν : ν ≠ 0) (i : K) :
    (nonsplitJ ν hν : Matrix (Fin 2) (Fin 2) K) * (matA9 i : Matrix (Fin 2) (Fin 2) K) =
      (matA9' ν i hν : Matrix (Fin 2) (Fin 2) K) *
        (nonsplitJ ν hν : Matrix (Fin 2) (Fin 2) K) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [nonsplitJ, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem exists_mem_invXiAut_order_four_nine [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) (h9 : Nat.card K = 9) {ν : K} (hν : ¬ IsSquare ν) :
    ∃ y : PSL2 K, y ∈ invXiAut (pgl2InnerAutPSL2 K hK hcard (N0 ν (ne_zero_of_not_isSquare hν))) ∧
      y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
  have hν0 := ne_zero_of_not_isSquare hν
  obtain ⟨i, hi, hν4, h3⟩ := exists_data_nine h9 hν
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hconj := pgl2InnerAutPSL2_N0_mk hK hcard ν hν0 (A := matA9 i) (A' := matA9' ν i hν0)
    (nonsplitJ_mul_matA9 ν hν0 i)
  set B : SL(2, K) := matA9' ν i hν0 * (matA9 i)⁻¹ with hB
  have hB00 : (B : Matrix (Fin 2) (Fin 2) K) 0 0 = -ν := by
    rw [hB]
    simp [mul_apply_SL]
  have hB01 : (B : Matrix (Fin 2) (Fin 2) K) 0 1 = -(ν * i) := by
    rw [hB]
    simp [mul_apply_SL]
  have hB11 : (B : Matrix (Fin 2) (Fin 2) K) 1 1 = -ν⁻¹ + i * i := by
    rw [hB]
    simp [mul_apply_SL]
  have hu : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν0
  have ht : (-ν - ν⁻¹ - 1) ^ 2 = (-ν - ν⁻¹ - 1) + 1 := by
    linear_combination (ν⁻¹ ^ 2) * hν4 + (-ν ^ 2 * (ν * ν⁻¹ + 1) + 2) * hu + (ν + ν⁻¹ + 1) * h3
  have hCH := sl2_mul_self B
  rw [hB00, hB11, hi, show -ν + (-ν⁻¹ + -1) = -ν - ν⁻¹ - 1 by ring] at hCH
  have hB5 : B ^ 5 = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    exact pow_five_eq_neg_one_of_mul_self hCH ht
  have hB1 : B ≠ 1 := fun h => by
    have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp only [hB01, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne, ne_eq,
      Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true] at this
    exact mul_ne_zero hν0 hi0 (neg_eq_zero.1 this)
  have hB2 : B ≠ -1 := fun h => by
    have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp only [hB01, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
      not_false_eq_true, neg_zero] at this
    exact mul_ne_zero hν0 hi0 (neg_eq_zero.1 this)
  have hCHA := sl2_mul_self (matA9 i)
  rw [show (matA9 i : Matrix (Fin 2) (Fin 2) K) 0 0 + (matA9 i : Matrix (Fin 2) (Fin 2) K) 1 1 = i
    by simp] at hCHA
  have hi2 : i ^ 2 = 2 := by linear_combination hi - h3
  have hA4 : matA9 i ^ 4 = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    exact pow_four_eq_neg_one_of_mul_self hCHA hi2
  have hA2 : (matA9 i ^ 2 : SL(2, K)) ≠ 1 ∧ (matA9 i ^ 2 : SL(2, K)) ≠ -1 := by
    have e : ((matA9 i ^ 2 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1 = i := by
      simp [pow_two, mul_apply_SL]
    constructor
    · intro h
      rw [h] at e
      simp at e
      exact hi0 e.symm
    · intro h
      rw [h] at e
      simp at e
      exact hi0 e.symm
  refine ⟨mk (matA9 i), mk_mem_invXiAut_of_pow_odd hconj (m := 5) (by decide) (Or.inr hB5) hB1 hB2,
    ?_, ?_⟩
  · rw [← map_pow, hA4, mk_neg, map_one]
  · rw [← map_pow, Ne, mk_eq_one_iff, not_or]
    exact hA2

end CFSG.Quasithin.F7Two
