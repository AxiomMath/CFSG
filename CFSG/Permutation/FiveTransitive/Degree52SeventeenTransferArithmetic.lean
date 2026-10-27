module

public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

namespace FiveTransitive.Degree52SeventeenTransferArithmetic

theorem multiplier_cases
    {H d k : ℕ} (hH : H = 16 ∨ H = 48) (hd : d ∣ 96)
    (hk : k % 17 = 1) (hprod : d * k * 17 = 311875200 * H) :
    d = 1 ∨ d = 3 := by
  have hdle := Nat.le_of_dvd (by norm_num : 0 < 96) hd
  interval_cases d <;> norm_num at hd
  all_goals rcases hH with rfl | rfl <;> omega

end FiveTransitive.Degree52SeventeenTransferArithmetic

end CFSG
