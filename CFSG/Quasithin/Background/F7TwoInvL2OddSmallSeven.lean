module

public import CFSG.Quasithin.Background.F7TwoInvL2OddSmallAlg
public import CFSG.Quasithin.Background.F7TwoInvL2OddNonsplit
public import CFSG.Dihedral.Glauberman.DicksonMaxNode

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GorensteinWalter CFSG.PSL2Table
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def lowerUnipSL (s : K) : SL(2, K) := ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem coe_lowerUnipSL (s : K) :
    (lowerUnipSL s : Matrix (Fin 2) (Fin 2) K) = !![1, 0; s, 1] := rfl

theorem nonsplitJ_mul_unip (ν : K) (hν : ν ≠ 0) (t : K) :
    (nonsplitJ ν hν : Matrix (Fin 2) (Fin 2) K) * (unip t : Matrix (Fin 2) (Fin 2) K) =
      (lowerUnipSL (t * ν⁻¹) : Matrix (Fin 2) (Fin 2) K) *
        (nonsplitJ ν hν : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nonsplitJ, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem exists_mul_self_eq_three_mul [Finite K] (h7 : Nat.card K = 7) {ν : K}
    (hν : ¬ IsSquare ν) : ∃ t : K, t * t = 3 * ν ∧ (3 : K) ≠ 0 ∧ (7 : K) = 0 := by
  let : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 7 := by rw [← Nat.card_eq_fintype_card]; exact h7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : CharP K 7 := charP_of_card_eq_prime_pow (p := 7) (f := 1) (by simpa using hcardK)
  have h7K : (7 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 7
  have hF : ringChar K ≠ 2 := by rw [ringChar.eq K 7]; norm_num
  have hν0 : ν ≠ 0 := ne_zero_of_not_isSquare hν
  have hhalf : Fintype.card K / 2 = 3 := by rw [hcardK]
  have hν3 : ν ^ 3 = -1 := by
    rcases FiniteField.pow_dichotomy hF hν0 with h | h
    · rw [hhalf] at h
      exact absurd ((FiniteField.isSquare_iff hF hν0).2 (by rwa [hhalf])) hν
    · rwa [hhalf] at h
  have h33 : (3 : K) ^ 3 = -1 := by linear_combination 4 * h7K
  have h3ne : (3 : K) ≠ 0 := fun h => by
    rw [h] at h33
    simp at h33
  have hsq : IsSquare (3 * ν) := by
    rw [FiniteField.isSquare_iff hF (mul_ne_zero h3ne hν0), hhalf, mul_pow, h33, hν3]
    norm_num
  obtain ⟨t, ht⟩ := hsq
  exact ⟨t, ht.symm, h3ne, h7K⟩

theorem exists_mem_invXiAut_orderOf_seven [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) (h7 : Nat.card K = 7) {ν : K} (hν : ¬ IsSquare ν) :
    ∃ y : PSL2 K, y ∈ invXiAut (pgl2InnerAutPSL2 K hK hcard (N0 ν (ne_zero_of_not_isSquare hν))) ∧
      orderOf y = 7 := by
  have hν0 := ne_zero_of_not_isSquare hν
  obtain ⟨t, ht, h3, h7K⟩ := exists_mul_self_eq_three_mul h7 hν
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact mul_ne_zero h3 hν0 (by rw [← ht, mul_zero])
  have hs : t * ν⁻¹ * ν = t := by field_simp
  have hst : t * ν⁻¹ * t = 3 := by
    have : t * ν⁻¹ * t = (t * t) * ν⁻¹ := by ring
    rw [this, ht]
    field_simp
  have hconj := pgl2InnerAutPSL2_N0_mk hK hcard ν hν0 (A := unip t) (A' := lowerUnipSL (t * ν⁻¹))
    (nonsplitJ_mul_unip ν hν0 t)
  set B : SL(2, K) := lowerUnipSL (t * ν⁻¹) * (unip t)⁻¹ with hB
  have hB01 : (B : Matrix (Fin 2) (Fin 2) K) 0 1 = -t := by
    rw [hB, unip_neg]
    simp [mul_apply_SL]
  have hB00 : (B : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    rw [hB, unip_neg]
    simp [mul_apply_SL]
  have hB11 : (B : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 - t * ν⁻¹ * t := by
    rw [hB, unip_neg]
    simp [mul_apply_SL]
    ring
  have hCH := sl2_mul_self B
  rw [hB00, hB11, hst, show (1 : K) + (1 - 3) = -1 by ring, neg_smul, one_smul] at hCH
  have hB3 : B ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact pow_three_eq_one_of_mul_self hCH
  have hB1 : B ≠ 1 := fun h => by
    have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp only [hB01, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne, ne_eq,
      Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true] at this
    exact ht0 (neg_eq_zero.1 this)
  have hB2 : B ≠ -1 := fun h => by
    have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp only [hB01, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
      not_false_eq_true, neg_zero] at this
    exact ht0 (neg_eq_zero.1 this)
  refine ⟨mk (unip t), mk_mem_invXiAut_of_pow_odd hconj (m := 3) (by decide) (Or.inl hB3) hB1 hB2,
    ?_⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, CFSG.Glauberman.Dickson.MaxNode.unip_pow]
    simp [h7K, unip_zero]
  · rw [Ne, mk_eq_one_iff, not_or]
    refine ⟨fun h => ht0 ?_, fun h => ht0 ?_⟩
    · simpa using congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
    · simpa using congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h

end CFSG.Quasithin.F7Two
