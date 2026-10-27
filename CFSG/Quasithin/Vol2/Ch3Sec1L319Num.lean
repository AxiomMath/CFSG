module

public import Mathlib.Data.Nat.Factors
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.H13.L319

theorem three_pow_mod_eight (a : ℕ) : 3 ^ a % 8 = 1 ∨ 3 ^ a % 8 = 3 := by
  induction a with
  | zero => left; norm_num
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem cartan_three_power {n a : ℕ} (hn : 2 ≤ n) (h : 2 ^ n - 1 = 3 ^ a) : n = 2 := by
  by_contra hne
  have h3 : 3 ≤ n := by omega
  obtain ⟨c, hc⟩ : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 h3
  have h8 : 2 ^ n = 8 * c := by
    rw [hc]
    norm_num
  have hpos : 0 < 2 ^ n := by positivity
  have hsum : 3 ^ a + 1 = 2 ^ n := by omega
  rcases three_pow_mod_eight a with h1 | h1 <;> omega

theorem cartan_three_power_of_primes {n : ℕ} (hn : 2 ≤ n)
    (hprime : ∀ {d : ℕ}, Nat.Prime d → d ∣ 2 ^ n - 1 → d = 3) : n = 2 := by
  have h4 : 4 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn
    simpa using this
  have hne : 2 ^ n - 1 ≠ 0 := by omega
  exact cartan_three_power hn (Nat.eq_prime_pow_of_unique_prime_dvd (p := 3) hne hprime)

end CFSG.Quasithin.H13.L319
