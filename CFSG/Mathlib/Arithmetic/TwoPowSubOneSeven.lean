module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

theorem three_dvd_iff_seven_dvd_two_pow_sub_one (m : ℕ) :
    3 ∣ m ↔ 7 ∣ 2 ^ m - 1 := by
  have hord : orderOf (2 : ZMod 7) = 3 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro k hk hk0
    interval_cases k <;> decide
  constructor
  · intro h3
    obtain ⟨k, rfl⟩ := h3
    have h1 : 7 ∣ 2 ^ 3 - 1 := by norm_num
    have := Nat.pow_sub_one_dvd_pow_sub_one 2 (show 3 ∣ 3 * k by omega)
    simpa [pow_mul] using h1.trans this
  · intro h7
    rw [← hord, orderOf_dvd_iff_pow_eq_one]
    have hd0 : ((2 ^ m - 1 : ℕ) : ZMod 7) = ((0 : ℕ) : ZMod 7) := by
      rw [ZMod.natCast_eq_natCast_iff']
      simpa using Nat.dvd_iff_mod_eq_zero.mp h7
    have hd : ((2 ^ m - 1 : ℕ) : ZMod 7) = 0 := by simpa using hd0
    have h1 : ((2 ^ m : ℕ) : ZMod 7) = 1 := by
      calc ((2 ^ m : ℕ) : ZMod 7) = ((2 ^ m - 1 + 1 : ℕ) : ZMod 7) := by
            rw [Nat.sub_add_cancel Nat.one_le_two_pow]
        _ = ((2 ^ m - 1 : ℕ) : ZMod 7) + 1 := by push_cast; ring
        _ = 1 := by rw [hd]; ring
    simpa [Nat.cast_pow] using h1

theorem eq_three_of_forall_prime_dvd_two_pow_sub_one (n : ℕ) (hnodd : Odd n) (hn2 : 2 ≤ n)
    (h : ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → p = 7) : n = 3 := by
  have hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ = 3 := by
    intro ℓ hℓ hℓn
    have hℓ3 : 3 ≤ ℓ := by
      rcases hℓ.eq_two_or_odd with h2 | ho
      · rw [h2] at hℓn
        have h1 : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hℓn
        have h2' : n % 2 = 1 := Nat.odd_iff.mp hnodd
        omega
      · have h2 : 2 ≤ ℓ := hℓ.two_le
        omega
    have hdiv : 2 ^ ℓ - 1 ∣ 2 ^ n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hℓn
    have hne : 2 ^ ℓ - 1 ≠ 1 := by
      have h1 : 2 ^ 3 ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ3
      omega
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
    have hq7 : q = 7 := h q hq (hqdvd.trans hdiv)
    have h7 : 7 ∣ 2 ^ ℓ - 1 := hq7 ▸ hqdvd
    have h3 : 3 ∣ ℓ := (three_dvd_iff_seven_dvd_two_pow_sub_one ℓ).mpr h7
    rcases (Nat.dvd_prime hℓ).mp h3 with h1 | h3'
    · exact absurd h1 (by norm_num)
    · exact h3'.symm
  have h3n : 3 ∣ n := by
    obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    exact (hprime ℓ hℓ hℓn) ▸ hℓn
  have h9n : ¬ 9 ∣ n := by
    intro h9
    have hdiv : 2 ^ 9 - 1 ∣ 2 ^ n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 h9
    have h73 : (73 : ℕ) ∣ 2 ^ n - 1 := (by norm_num : (73 : ℕ) ∣ 2 ^ 9 - 1).trans hdiv
    have := h 73 (by norm_num) h73
    norm_num at this
  obtain ⟨m, rfl⟩ := h3n
  have hm3 : ¬ 3 ∣ m := by
    intro h3m
    obtain ⟨k, hk⟩ := h3m
    exact h9n ⟨k, by rw [hk]; ring⟩
  have hm1 : m = 1 := by
    by_contra hm1
    have hm2 : 2 ≤ m := by omega
    obtain ⟨ℓ, hℓ, hℓm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    have hℓ3 : ℓ = 3 := hprime ℓ hℓ (Dvd.dvd.mul_left hℓm 3)
    exact hm3 (hℓ3 ▸ hℓm)
  rw [hm1]

end CFSG
