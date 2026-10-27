module

public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.StandardType.FF81.RootFusionLin

theorem choose_add_lt_choose (N r d : ℕ) (hN : N = 8 ∨ N = 9) (hr : 2 ≤ r) (h2r : 2 * r ≤ N)
    (hd : d ≤ N - 1) (hd8 : N = 8 → r = 4 → d ≤ 1) :
    (N - 2).choose 2 + d + r.choose 2 < N.choose 2 := by
  have hr4 : r ≤ 4 := by omega
  rcases hN with rfl | rfl
  · interval_cases r
    · simp [Nat.choose] at *; omega
    · simp [Nat.choose] at *; omega
    · simp [Nat.choose] at *; omega
  · interval_cases r
    · simp [Nat.choose] at *; omega
    · simp [Nat.choose] at *; omega
    · simp [Nat.choose] at *; omega

theorem padicValNat_le_of_le_two_pow {n k : ℕ} (hn : 0 < n) (h : n ≤ 2 ^ k) :
    padicValNat 2 n ≤ k := by
  have h1 : 2 ^ padicValNat 2 n ∣ n := pow_padicValNat_dvd
  have h2 : 2 ^ padicValNat 2 n ≤ 2 ^ k := (Nat.le_of_dvd hn h1).trans h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

end CFSG.StandardType.FF81.RootFusionLin

end
