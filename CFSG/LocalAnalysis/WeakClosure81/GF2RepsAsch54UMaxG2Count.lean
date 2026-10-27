module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

import CFSG.Timmesfeld.Orders.ClassicalHypSum

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80G2

open scoped MatrixGroups

private theorem g2Count_sq_iff {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (A : SL(2, F)) :
    A * A = -1 ↔ A 1 1 = -A 0 0 := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h := A.2
    rwa [Matrix.det_fin_two] at h
  constructor
  · intro h
    have e00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = -1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using
        (Matrix.SpecialLinearGroup.ext_iff _ _ |>.mp h) 0 0
    have e01 : A 0 0 * A 0 1 + A 0 1 * A 1 1 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using
        (Matrix.SpecialLinearGroup.ext_iff _ _ |>.mp h) 0 1
    have e10 : A 1 0 * A 0 0 + A 1 1 * A 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using
        (Matrix.SpecialLinearGroup.ext_iff _ _ |>.mp h) 1 0
    have e11 : A 1 0 * A 0 1 + A 1 1 * A 1 1 = -1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using
        (Matrix.SpecialLinearGroup.ext_iff _ _ |>.mp h) 1 1
    by_contra hne
    have hs : A 1 1 + A 0 0 ≠ 0 := fun h' => hne (by linear_combination h')
    have hb : A 0 1 = 0 := by
      have : A 0 1 * (A 1 1 + A 0 0) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : A 1 0 = 0 := by
      have : A 1 0 * (A 1 1 + A 0 0) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    have had : A 1 1 = A 0 0 := by
      have : (A 1 1 - A 0 0) * (A 1 1 + A 0 0) = 0 := by linear_combination e11 - e00
      have := (mul_eq_zero.mp this).resolve_right hs
      linear_combination this
    apply h2
    linear_combination A 0 0 * had - 2 * A 1 0 * hb + e00 - hdet
  · intro h
    rw [Matrix.SpecialLinearGroup.ext_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-1 : F) * hdet + A 0 0 * h
    · linear_combination A 0 1 * h
    · linear_combination A 1 0 * h
    · linear_combination (-1 : F) * hdet + A 1 1 * h

private def g2CountEquiv {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    {A : SL(2, F) // A * A = -1} ≃ Σ a : F, {p : F × F // p.1 * p.2 + (1 + a ^ 2) = 0} where
  toFun A := ⟨A.1 0 0, (A.1 0 1, A.1 1 0), by
    have hd := (g2Count_sq_iff h2 A.1).mp A.2
    have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
      have h := A.1.2
      rwa [Matrix.det_fin_two] at h
    rw [hd] at hdet
    linear_combination -hdet⟩
  invFun x := ⟨⟨!![x.1, x.2.1.1; x.2.1.2, -x.1], by
      rw [Matrix.det_fin_two_of]
      linear_combination -x.2.2⟩, (g2Count_sq_iff h2 _).mpr (by simp)⟩
  left_inv A := by
    have hd := (g2Count_sq_iff h2 A.1).mp A.2
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hd]
  right_inv x := by
    rcases x with ⟨a, ⟨b, c⟩, hbc⟩
    rfl

private theorem g2Count_card_roots {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (h2 : (2 : F) ≠ 0) :
    (Finset.univ.filter fun a : F => 1 + a ^ 2 = 0).card =
      if IsSquare (-1 : F) then 2 else 0 := by
  split_ifs with hsq
  · obtain ⟨i, hi⟩ := hsq
    have hi0 : i ≠ 0 := by
      rintro rfl
      simp at hi
    have hne : i ≠ -i := by
      intro h
      have : (2 : F) * i = 0 := by linear_combination h
      exact mul_ne_zero h2 hi0 this
    have hset : (Finset.univ.filter fun a : F => 1 + a ^ 2 = 0) = {i, -i} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro ha
        have : (a - i) * (a + i) = 0 := by linear_combination ha + hi
        rcases mul_eq_zero.mp this with h | h
        · exact Or.inl (sub_eq_zero.mp h)
        · exact Or.inr (eq_neg_of_add_eq_zero_left h)
      · rintro (rfl | rfl) <;> linear_combination -hi
    rw [hset, Finset.card_pair hne]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a _ ha
    exact hsq ⟨a, by linear_combination -ha⟩

theorem card_sl2_sq_eq_neg_one_mod_four {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card {A : SL(2, F) // A * A = -1} % 4 = 2 := by
  classical
  have := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at this
    exact_mod_cast this
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have hs := g2Count_card_roots h2
  rw [Nat.card_congr (g2CountEquiv h2), Nat.card_sigma]
  simp_rw [CFSG.Timmesfeld.ClassicalOrders.card_mul_add_eq_zero]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero, Finset.card_univ, smul_eq_mul, smul_eq_mul, hs,
    ← Nat.card_eq_fintype_card]
  by_cases hsq : IsSquare (-1 : F)
  · have h4 : Fintype.card F % 4 ≠ 3 := FiniteField.isSquare_neg_one_iff.mp hsq
    rw [if_pos hsq]
    rw [← Nat.card_eq_fintype_card] at h4 hodd
    obtain ⟨k, hk⟩ : ∃ k, Nat.card F = 4 * k + 1 := ⟨Nat.card F / 4, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    have : (4 * k + 1) * (4 * k) + 2 * (4 * k + 1) = 4 * (4 * k * k + 3 * k) + 2 := by ring
    omega
  · have h4 : ¬ Fintype.card F % 4 ≠ 3 := fun h => hsq (FiniteField.isSquare_neg_one_iff.mpr h)
    rw [if_neg hsq]
    rw [← Nat.card_eq_fintype_card] at h4 hodd
    obtain ⟨k, hk⟩ : ∃ k, Nat.card F = 4 * k + 3 := ⟨Nat.card F / 4, by omega⟩
    have h' : 4 * k + 3 - 1 = 4 * k + 2 := by omega
    rw [hk, h']
    have : (4 * k + 3) * (4 * k + 2) + 0 * (4 * k + 3) = 4 * (4 * k * k + 5 * k + 1) + 2 := by
      ring
    omega

theorem card_sq_eq_of_equiv_sl2 {Y : Type} [Group Y] {J : Subgroup Y} {F : Type} [Field F]
    (e : ↥J ≃* SL(2, F)) {z : Y} (hz : z ∈ J) (hez : e ⟨z, hz⟩ = -1) :
    Nat.card {a : Y // a ∈ J ∧ a * a = z} = Nat.card {A : SL(2, F) // A * A = -1} := by
  refine Nat.card_congr
    { toFun := fun a => ⟨e ⟨a.1, a.2.1⟩, ?_⟩
      invFun := fun A => ⟨(e.symm A : Y), (e.symm A).2, ?_⟩
      left_inv := fun a => ?_
      right_inv := fun A => ?_ }
  · have h : (⟨a.1, a.2.1⟩ : ↥J) * ⟨a.1, a.2.1⟩ = ⟨z, hz⟩ := Subtype.ext a.2.2
    rw [← map_mul, h, hez]
  · have h : e.symm A * e.symm A = ⟨z, hz⟩ := by
      rw [← map_mul, A.2, ← hez, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h
  · simp
  · simp

end CFSG.LocalAnalysis.WeakClosure81.Asch80G2

end
