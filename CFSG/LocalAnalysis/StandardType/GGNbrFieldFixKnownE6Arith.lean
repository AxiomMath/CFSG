module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType

theorem two_lt_two_pow_div_of_dvd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n)
    (hn : 1 ≤ n) (hF : p ∣ 2 ^ n - 1) : 2 < 2 ^ (n / p) := by
  obtain ⟨m, rfl⟩ := hpn
  have hp_pos : 0 < p := hp.pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hn
  rw [Nat.mul_div_cancel_left m hp_pos]
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ 2 ^ m - 1 := by
    have h0 : ((2 ^ (p * m) - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hF
    rw [Nat.cast_sub Nat.one_le_two_pow] at h0
    push_cast at h0
    have h1 : (2 : ZMod p) ^ (p * m) = 1 := sub_eq_zero.mp h0
    have h2 : (2 : ZMod p) ^ m = 1 := by
      rw [mul_comm p m, pow_mul, ZMod.pow_card] at h1
      exact h1
    have h3 : ((2 ^ m - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      rw [h2, sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).mp h3
  have hpos : 0 < 2 ^ m - 1 := by
    have h := Nat.one_lt_two_pow hm0
    omega
  have hle : p ≤ 2 ^ m - 1 := Nat.le_of_dvd hpos hdvd
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  omega

end CFSG.StandardType

end
