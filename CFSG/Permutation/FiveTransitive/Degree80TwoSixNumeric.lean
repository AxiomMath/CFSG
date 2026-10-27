module

public import CFSG.Permutation.FiveTransitive.Degree79TwoFiveNumeric

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoSixNumeric
private theorem geometry (a b c d e f : ℕ)
    (htotal : 74 = 2*a + 4*b + 8*c + 16*d + 32*e + 64*f)
    (h3 : 2*(a%3) + b%3 + 2*(c%3) + d%3 + 2*(e%3) + f%3 ≤ 2)
    (h5 : 2*(a%5) + 4*(b%5) + 3*(c%5) + d%5 + 2*(e%5) + 4*(f%5) ≤ 4) :
    (a = 37 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0) ∨
      (a = 27 ∧ b = 5 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0) ∨
      (a = 25 ∧ b = 6 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0) ∨
      (a = 15 ∧ b = 11 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0) ∨
      (a = 7 ∧ b = 15 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0) ∨
      (a = 21 ∧ b = 0 ∧ c = 0 ∧ d = 2 ∧ e = 0 ∧ f = 0) ∨
      (a = 21 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 1 ∧ f = 0) := by
  have hcoarse := Degree79TwoFiveNumeric.geometry a b c d e f htotal h3 h5
  rcases hcoarse with ha | ⟨hc,hd,he,hf,hb⟩
  · have hf : f = 0 := by omega
    subst f
    have he : e ≤ 1 := by omega
    have hd : d ≤ 2 := by omega
    have hc : c ≤ 4 := by omega
    interval_cases e <;> interval_cases d <;> interval_cases c <;> try omega
    all_goals
      have hb : b ≤ 9 := by omega
      interval_cases b <;> omega
  · subst c; subst d; subst e; subst f
    have hb18 : b ≤ 18 := by omega
    interval_cases b <;> omega
theorem all_pairs (a b c d e f : ℕ)
    (htotal : 74 = 2*a + 4*b + 8*c + 16*d + 32*e + 64*f)
    (h3 : 2*(a%3) + b%3 + 2*(c%3) + d%3 + 2*(e%3) + f%3 ≤ 2)
    (h5 : 2*(a%5) + 4*(b%5) + 3*(c%5) + d%5 + 2*(e%5) + 4*(f%5) ≤ 4)
    (hb : 9 ∣ b) (hd : 9 ∣ d) (he : 9 ∣ e) :
    a = 37 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  have hh := geometry a b c d e f htotal h3 h5
  rcases hh with hh | hh | hh | hh | hh | hh | hh <;> omega

end FiveTransitive.Degree80TwoSixNumeric

end CFSG
