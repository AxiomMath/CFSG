module

public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.D2Tools

public section

namespace CFSG.Quasithin

namespace B45Alt

variable {V : Type} [CommGroup V] [Finite V]

theorem index_le_sq_of_rAV_le_two (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsA2 X A) (h : rAV A ≤ 2) : (fixV A).index ≤ Nat.card A ^ 2 := by
  have hmul := hA.rAV_mul
  have hpos : (0 : ℚ) < (rk A : ℚ) := by exact_mod_cast hA.rk_pos
  have h1 : (rkIdx (fixV A) : ℚ) ≤ 2 * (rk A : ℚ) := by
    rw [← hmul]
    exact mul_le_mul_of_nonneg_right h hpos.le
  have h2 : rkIdx (fixV A) ≤ 2 * rk A := by exact_mod_cast h1
  rw [B1.index_eq_two_pow hV, B1.card_elemAbelian hA.isElemAbelian2, ← pow_mul, mul_comm]
  exact Nat.pow_le_pow_right (by norm_num) h2

theorem exists_cubic_of_qhatOf_le_two (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    (h : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    ∃ A, IsA2 G A ∧ commSeries A 3 = ⊥ ∧ (fixV A).index ≤ Nat.card A ^ 2 := by
  obtain ⟨A, hA, h3, hr⟩ := kq_le_iff.mp h
  exact ⟨A, hA, h3, index_le_sq_of_rAV_le_two hV hA hr⟩

theorem qhatOf_le_one_of_index_le (hV : ∀ v : V, v ^ 2 = 1) {G A : Subgroup (MulAut V)}
    (hA : IsA2 G A) (h3 : commSeries A 3 = ⊥) (h : (fixV A).index ≤ Nat.card A) :
    qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  refine kq_le_iff.mpr ⟨A, hA, h3, (rAV_le_one_iff hV hA).mpr ?_⟩
  rw [B1.card_eq_index_mul A]
  exact Nat.mul_le_mul_right _ h

theorem qhatOf_le_one_of_four (hV : ∀ v : V, v ^ 2 = 1) {G A : Subgroup (MulAut V)}
    (hAG : A ≤ G) (hA : IsElemAbelian2 A) (h4 : Nat.card A = 4)
    (h : Nat.card V ≤ 4 * Nat.card (fixV A)) : qhatOf G ≤ ((1 : ℚ) : WithTop ℚ) := by
  have hA1 : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h4
    exact absurd h4 (by norm_num)
  refine qhatOf_le_one_of_index_le hV ⟨hAG, hA1, hA⟩
    (commSeries_three_eq_bot_of_card_four hV hA h4) ?_
  rw [h4]
  have e := B1.card_eq_index_mul A (V := V)
  have hpos := B1.card_fixV_pos A
  rw [e] at h
  exact Nat.le_of_mul_le_mul_right h hpos

end B45Alt

end CFSG.Quasithin
