module

public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

namespace FiveTransitive.A6OrderArithmetic

theorem sixty_or_full (n d : ℕ) (h30 : 30 ∣ n) (hn : n ≤ 360)
    (hne : n ≠ 30) (hprod : d * n = 360) (hbound : 360 ≤ d.factorial) :
    n = 60 ∨ n = 360 := by
  obtain ⟨m,rfl⟩ := h30
  have hm : m ≤ 12 := by omega
  interval_cases m <;> norm_num at *
  all_goals
    first
    | omega
    | have hd : d ≤ 4 := by omega
      have hf := Nat.factorial_le hd
      norm_num [Nat.factorial] at hf
      omega

end FiveTransitive.A6OrderArithmetic

end CFSG
