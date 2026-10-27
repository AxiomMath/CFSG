module

public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

namespace FiveTransitive.TwoPowerModFive

theorem eq_sixteen_of_proper_divisor
    (n d : ℕ) (hpow : ∃ k : ℕ, n = 2 ^ k) (hn : n ≤ 16)
    (hd : d ∣ n) (hlt : d < n) (hmod : n % 5 = d % 5) :
    n = 16 := by
  obtain ⟨k, rfl⟩ := hpow
  have hk : k ≤ 4 := by
    by_contra h
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 5 ≤ k by omega)
    norm_num at hp
    omega
  interval_cases k <;> norm_num at *
  all_goals first | omega | (interval_cases d <;> norm_num at *)

end FiveTransitive.TwoPowerModFive

end CFSG
