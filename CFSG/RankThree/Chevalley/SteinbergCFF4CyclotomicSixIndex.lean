module

public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicCentralizers

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

theorem odd_sq_sub_self_add_one (q : ℕ) : Odd (q ^ 2 - q + 1) := by
  have h : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h]
  exact (Nat.even_mul_pred_self q).add_one

theorem le_sq_self (q : ℕ) : q ≤ q ^ 2 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact le_rfl
  · rw [sq]
    exact Nat.le_mul_of_pos_left q hq

theorem zmod_phiSix_eq_zero {p q : ℕ} (hpd : p ∣ q ^ 2 - q + 1) :
    (q : ZMod p) ^ 2 - q + 1 = 0 := by
  have h := (ZMod.natCast_eq_zero_iff _ p).2 hpd
  push_cast [Nat.cast_sub (le_sq_self q)] at h
  exact h

theorem ne_zero_of_dvd_phiSix {p q : ℕ} [Fact p.Prime] (hpd : p ∣ q ^ 2 - q + 1) :
    (q : ZMod p) ≠ 0 := by
  intro h
  have hf := zmod_phiSix_eq_zero hpd
  rw [h] at hf
  exact one_ne_zero (by linear_combination hf : (1 : ZMod p) = 0)

theorem F4_not_dvd_index_phiSix
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1) (T : Subgroup (adjointGroup .F4 K))
    (hT : Nat.card T = (Nat.card K ^ 2 - Nat.card K + 1) ^ 2) : ¬ p ∣ T.index := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hcard := T.card_mul_index
  rw [hT, card_adjointGroup_F4, CFSG.Open.ordF4] at hcard
  set Q : ℤ := (Nat.card K : ℤ) with hQ
  have hdZ : ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) = Q ^ 2 - Q + 1 := by
    rw [Nat.cast_add, Nat.cast_sub (le_sq_self _), Nat.cast_pow, Nat.cast_one]
  have hcardZ : (Q ^ 2 - Q + 1) ^ 2 * T.index =
      Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) hcard
    rw [Nat.cast_mul, Nat.cast_pow, hdZ] at h
    push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq1)] at h
    exact h
  have hd0 : (Q ^ 2 - Q + 1) ^ 2 ≠ 0 := by
    have hpos : 0 < Q ^ 2 - Q + 1 := by
      have hQ1 : 1 ≤ Q := by
        rw [hQ]
        exact_mod_cast hq1
      nlinarith
    positivity
  have hidx : (T.index : ℤ) =
      Q ^ 24 * (Q ^ 3 - 1) ^ 2 * (Q + 1) ^ 2 * (Q ^ 6 + 1) * (Q ^ 8 - 1) * (Q ^ 2 - 1) := by
    apply mul_left_cancel₀ hd0
    rw [hcardZ]
    ring
  have two : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_zmod_ne_zero_of_pos_of_lt (by norm_num) (by omega : 2 < p)
  have three : (3 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_zmod_ne_zero_of_pos_of_lt (by norm_num) hp3
  set x : ZMod p := ((Nat.card K : ℕ) : ZMod p) with hx
  have hf : x ^ 2 - x + 1 = 0 := zmod_phiSix_eq_zero hpd
  intro hdvd
  have hi : ((T.index : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hdvd
  have h0 := congrArg (Int.cast : ℤ → ZMod p) hidx
  push_cast at h0
  rw [show ((Q : ℤ) : ZMod p) = x by rw [hQ, Int.cast_natCast], hi] at h0
  refine (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_)
    ?_) h0.symm
  · exact pow_ne_zero _ (ne_zero_of_dvd_phiSix hpd)
  · exact pow_ne_zero _ fun h => two (by linear_combination (x + 1) * hf - h)
  · exact pow_ne_zero _ fun h => three (by linear_combination hf - (x - 2) * h)
  · exact fun h => two (by linear_combination h - (x ^ 4 + x ^ 3 - x - 1) * hf)
  · exact fun h => three (by
      linear_combination (1 + (x + 1) * (x ^ 6 + x ^ 5 - x ^ 3 - x ^ 2 + 1)) * hf - (x + 1) * h)
  · exact fun h => three (by linear_combination (x + 2) * hf - (x + 1) * h)

end CFSG.RankThree.Chevalley
