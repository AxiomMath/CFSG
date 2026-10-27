module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.ShultStronglyClosedTI.CoprimePrime

theorem suzuki_factor_eq {q : ℕ} (hq : 1 ≤ q) : q ^ 2 - q + 1 = q * (q - 1) + 1 := by
  have h : q ^ 2 = q * (q - 1) + q := by
    rw [Nat.mul_sub, mul_one, pow_two, Nat.sub_add_cancel (Nat.le_mul_of_pos_left q hq)]
  rw [h, Nat.add_sub_cancel]

theorem prime_not_dvd_of_dvd_suzuki_factor {q p : ℕ} (hq : 1 ≤ q) (hp : p.Prime)
    (hpN : p ∣ q ^ 2 - q + 1) : ¬ p ∣ q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
  rw [suzuki_factor_eq hq] at hpN
  have hnot : ¬ p ∣ q * (q - 1) := fun hdvd =>
    hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hdvd).mp hpN))
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h12 | h3
  · rcases (Nat.Prime.dvd_mul hp).mp h12 with h1 | h2
    · exact hnot (Dvd.dvd.mul_right (hp.dvd_of_dvd_pow h1) _)
    · exact hnot (Dvd.dvd.mul_left h2 _)
  · have hsum : q ^ 2 + 1 = (q * (q - 1) + 1) + q := by
      rw [← suzuki_factor_eq hq]
      have : q ≤ q ^ 2 := by nlinarith
      omega
    rw [hsum] at h3
    exact hnot (Dvd.dvd.mul_right ((Nat.dvd_add_right hpN).mp h3) _)

theorem prime_eq_three_of_dvd_suzuki_factor {p a : ℕ} (hp : p.Prime)
    (hpN : p ∣ (2 ^ p ^ a) ^ 2 - 2 ^ p ^ a + 1) : p = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ 2 ^ p ^ a := Nat.one_le_two_pow
  rw [suzuki_factor_eq hq] at hpN
  have h0 := (ZMod.natCast_eq_zero_iff _ p).mpr hpN
  push_cast [Nat.cast_sub hq] at h0
  have h2 : (2 : ZMod p) ^ p ^ a = 2 := ZMod.pow_card_pow 2
  rw [h2] at h0
  have h3 : ((3 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h0
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
    ((ZMod.natCast_eq_zero_iff _ p).mp h3)

end CFSG.ShultStronglyClosedTI.CoprimePrime
