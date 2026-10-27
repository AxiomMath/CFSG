module

public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.Quasithin.Background.F7TwoInvBasic

public section

namespace CFSG.Quasithin.F7Two

open scoped MatrixGroups
open CFSG.CGT.Timmesfeld75

variable {F : Type} [Field F] [CharP F 2]

theorem trace_mul_self_sl2 (A : SL(2, F)) :
    (A * A) 0 0 + (A * A) 1 1 = (A 0 0 + A 1 1) ^ 2 := by
  rw [mul_apply_00, mul_apply_11]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (A 0 1 * A 1 0 - A 0 0 * A 1 1) * h2

theorem trace_pow_two_pow_sl2 (A : SL(2, F)) (n : ℕ) :
    (A ^ 2 ^ n) 0 0 + (A ^ 2 ^ n) 1 1 = (A 0 0 + A 1 1) ^ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : A ^ 2 ^ (n + 1) = A ^ 2 ^ n * A ^ 2 ^ n := by rw [pow_succ 2 n, pow_mul, sq]
    rw [e, trace_mul_self_sl2, ih, ← pow_mul, pow_succ 2 n]

theorem not_isPGroup_two_zpowers_sl2 {A : SL(2, F)} (h : A 0 0 + A 1 1 ≠ 0) :
    ¬ IsPGroup 2 ↥(Subgroup.zpowers A) := by
  rw [isPGroup_two_zpowers_iff]
  rintro ⟨n, hn⟩
  have h1 := trace_pow_two_pow_sl2 A n
  rw [hn, one_apply_00, one_apply_11, CharTwo.add_self_eq_zero] at h1
  exact h (pow_eq_zero_iff (pow_ne_zero n two_ne_zero) |>.1 h1.symm)

section Antidiag

variable {W : SL(2, F)} (hW00 : W 0 0 = 0) (hW11 : W 1 1 = 0)
include hW00 hW11

theorem antidiag_det : W 0 1 * W 1 0 = 1 := by
  have h := sl2_det W
  rw [hW00, hW11] at h
  have h1 : W 0 1 * W 1 0 = - 1 := by linear_combination -h
  rw [h1, CharTwo.neg_eq]

theorem antidiag_ne_zero_01 : W 0 1 ≠ 0 := fun h => by
  have := antidiag_det hW00 hW11
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem antidiag_ne_zero_10 : W 1 0 ≠ 0 := fun h => by
  have := antidiag_det hW00 hW11
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem conj_utriElt_antidiag (b : F) : W * utriElt b * W⁻¹ = ltriElt (W 1 0 ^ 2 * b) := by
  have hd := antidiag_det hW00 hW11
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply sl2_ext
  · simp only [mul_apply_00, mul_apply_01, inv_apply_00, 
      inv_apply_10, utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
      utriElt_apply_11, ltriElt_apply_00, hW00, hW11]
    linear_combination -hd - h2
  · simp only [mul_apply_00, mul_apply_01, inv_apply_01,
      inv_apply_11, utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
      utriElt_apply_11, ltriElt_apply_01, hW00]
    ring
  · simp only [mul_apply_10, mul_apply_11, inv_apply_00, 
      inv_apply_10, utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
      utriElt_apply_11, ltriElt_apply_10, hW11]
    linear_combination (-(W 1 0 ^ 2 * b)) * h2
  · simp only [mul_apply_10, mul_apply_11, inv_apply_01,
      inv_apply_11, utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
      utriElt_apply_11, ltriElt_apply_11, hW00, hW11]
    linear_combination -hd - h2

theorem conj_ltriElt_antidiag (c : F) : W * ltriElt c * W⁻¹ = utriElt (W 0 1 ^ 2 * c) := by
  have hd := antidiag_det hW00 hW11
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply sl2_ext
  · simp only [mul_apply_00, mul_apply_01, inv_apply_00, 
      inv_apply_10, utriElt_apply_00, ltriElt_apply_00, ltriElt_apply_01,
      ltriElt_apply_10, ltriElt_apply_11, hW00, hW11]
    linear_combination -hd - h2
  · simp only [mul_apply_00, mul_apply_01, inv_apply_01,
      inv_apply_11, utriElt_apply_01, ltriElt_apply_00, ltriElt_apply_01,
      ltriElt_apply_10, ltriElt_apply_11, hW00]
    linear_combination (-(W 0 1 ^ 2 * c)) * h2
  · simp only [mul_apply_10, mul_apply_11, inv_apply_00, 
      inv_apply_10, utriElt_apply_10, ltriElt_apply_00, ltriElt_apply_01,
      ltriElt_apply_10, ltriElt_apply_11, hW11]
    ring
  · simp only [mul_apply_10, mul_apply_11, inv_apply_01,
      inv_apply_11, utriElt_apply_11, ltriElt_apply_00, ltriElt_apply_01,
      ltriElt_apply_10, ltriElt_apply_11, hW00, hW11]
    linear_combination -hd - h2

theorem utri_sup_conj_eq_top :
    utri F ⊔ (utri F).map (MulAut.conj W).toMonoidHom = ⊤ := by
  have hw : W 1 0 ≠ 0 := antidiag_ne_zero_10 hW00 hW11
  refine eq_top_iff.2 (utri_sup_ltri (F := F) ▸ sup_le le_sup_left fun g hg => ?_)
  obtain ⟨c, rfl⟩ := mem_ltri_iff.1 hg
  refine Subgroup.mem_sup_right ⟨utriElt (c / W 1 0 ^ 2), mem_utri_iff.2 ⟨_, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [conj_utriElt_antidiag hW00 hW11, mul_div_cancel₀ _ (pow_ne_zero 2 hw)]

theorem ltri_sup_conj_eq_top :
    ltri F ⊔ (ltri F).map (MulAut.conj W).toMonoidHom = ⊤ := by
  have hw : W 0 1 ≠ 0 := antidiag_ne_zero_01 hW00 hW11
  refine eq_top_iff.2 (utri_sup_ltri (F := F) ▸ sup_le (fun g hg => ?_) le_sup_left)
  obtain ⟨s, rfl⟩ := mem_utri_iff.1 hg
  refine Subgroup.mem_sup_right ⟨ltriElt (s / W 0 1 ^ 2), mem_ltri_iff.2 ⟨_, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [conj_ltriElt_antidiag hW00 hW11, mul_div_cancel₀ _ (pow_ne_zero 2 hw)]

theorem not_isPGroup_utri_mul_conj :
    ¬ IsPGroup 2 ↥(Subgroup.zpowers (utriElt (1 : F) * (W * utriElt 1 * W⁻¹))) := by
  refine not_isPGroup_two_zpowers_sl2 ?_
  rw [conj_utriElt_antidiag hW00 hW11, mul_apply_00, mul_apply_11, utriElt_apply_00,
    utriElt_apply_01, utriElt_apply_10, utriElt_apply_11, ltriElt_apply_00, ltriElt_apply_01,
    ltriElt_apply_10, ltriElt_apply_11, mul_one]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  intro h
  exact pow_ne_zero 2 (antidiag_ne_zero_10 hW00 hW11) (by linear_combination h - h2)

theorem not_isPGroup_ltri_mul_conj :
    ¬ IsPGroup 2 ↥(Subgroup.zpowers (ltriElt (1 : F) * (W * ltriElt 1 * W⁻¹))) := by
  refine not_isPGroup_two_zpowers_sl2 ?_
  rw [conj_ltriElt_antidiag hW00 hW11, mul_apply_00, mul_apply_11, utriElt_apply_00,
    utriElt_apply_01, utriElt_apply_10, utriElt_apply_11, ltriElt_apply_00, ltriElt_apply_01,
    ltriElt_apply_10, ltriElt_apply_11, mul_one]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  intro h
  exact pow_ne_zero 2 (antidiag_ne_zero_01 hW00 hW11) (by linear_combination h - h2)

end Antidiag

end CFSG.Quasithin.F7Two
