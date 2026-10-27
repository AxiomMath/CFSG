module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoTwelveOrbitNumeric

theorem alternatives (a b c d e f : ℕ)
    (hm : 2*a + 4*b + 8*c + 16*d + 32*e + 64*f = 68)
    (hb : 2*(a%11) + 4*(b%11) + 8*(c%11) + 16*(d%11) + 32*(e%11) + 64*(f%11) ≤ 3) :
    c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧
      ((a = 34 ∧ b = 0) ∨ (a = 12 ∧ b = 11)) := by
  omega

end FiveTransitive.Degree80TwoTwelveOrbitNumeric

end CFSG
