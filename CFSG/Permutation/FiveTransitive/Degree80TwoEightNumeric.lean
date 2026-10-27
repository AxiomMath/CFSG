module

public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoEightNumeric
theorem geometry (a b c d e f : ℕ)
    (htotal : 72 = 2*a + 4*b + 8*c + 16*d + 32*e + 64*f)
    (h5 : 2*(a%5) + 4*(b%5) + 3*(c%5) + d%5 + 2*(e%5) + 4*(f%5) ≤ 2)
    (h7 : 2*(a%7) + 4*(b%7) + c%7 + 2*(d%7) + 4*(e%7) + f%7 ≤ 2) :
    a = 36 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  have hf : f ≤ 1 := by omega
  have he : e ≤ 2 := by omega
  have hd : d ≤ 4 := by omega
  have hc : c ≤ 9 := by omega
  interval_cases f <;> interval_cases e <;> interval_cases d <;> interval_cases c <;> omega
end FiveTransitive.Degree80TwoEightNumeric

end CFSG
