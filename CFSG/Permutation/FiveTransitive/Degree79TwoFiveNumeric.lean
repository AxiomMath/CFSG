module

public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

namespace FiveTransitive.Degree79TwoFiveNumeric
theorem geometry (a b c d e f : ℕ)
    (htotal : 74 = 2*a + 4*b + 8*c + 16*d + 32*e + 64*f)
    (h3 : 2*(a%3) + b%3 + 2*(c%3) + d%3 + 2*(e%3) + f%3 ≤ 2)
    (h5 : 2*(a%5) + 4*(b%5) + 3*(c%5) + d%5 + 2*(e%5) + 4*(f%5) ≤ 4) :
    18 ≤ a ∨ (c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ 6 ≤ b) := by
  have hf : f ≤ 1 := by omega
  have he : e ≤ 2 := by omega
  have hd : d ≤ 4 := by omega
  have hc : c ≤ 9 := by omega
  interval_cases f <;> interval_cases e <;> interval_cases d <;> interval_cases c <;> try omega
  all_goals
    have hb : b ≤ 2 := by omega
    interval_cases b <;> norm_num at *
    all_goals omega
end FiveTransitive.Degree79TwoFiveNumeric

end CFSG
