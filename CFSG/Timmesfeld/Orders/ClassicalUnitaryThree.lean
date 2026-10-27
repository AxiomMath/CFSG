module

public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Timmesfeld.ClassicalOrders

open CFSG.Assembly.LowTwoRank

theorem card_psu_three_mul_gcd {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  have key : Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) =
      (p ^ f) ^ (3 * (3 - 1) / 2) *
        (∏ i ∈ Finset.Icc 2 3, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
          Nat.gcd 3 (p ^ f + 1) :=
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (by norm_num : 2 ≤ 3)
  rw [key]
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat =
      ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    refine congrArg₂ (· * ·) ?_ ?_
    · have : (((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2) = (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) := by
        have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
        push_cast [Nat.cast_sub this]
        ring
      rw [this, Int.toNat_natCast]
    · have : (((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3) = (((p ^ f) ^ 3 + 1 : ℕ) : ℤ) := by
        push_cast
        ring_nf
      rw [this, Int.toNat_natCast]
  rw [hprod]
  have hdvd : Nat.gcd 3 (p ^ f + 1) ∣ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
    have := Odd.nat_add_dvd_pow_add_pow (p ^ f) 1 (by decide : Odd 3)
    simp only [one_pow] at this
    exact (Nat.gcd_dvd_right 3 _).trans this
  have : (p ^ f) ^ (3 * (3 - 1) / 2) = (p ^ f) ^ 3 := by norm_num
  rw [this]
  exact Nat.div_mul_cancel hdvd

end CFSG.Timmesfeld.ClassicalOrders
