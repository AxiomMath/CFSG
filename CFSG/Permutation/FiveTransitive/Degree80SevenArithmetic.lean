module

public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree80SevenArithmetic

theorem normalizer_prime
    (f : ℕ) (hlo : 5 ≤ f) (hhi : f ≤ 40) (hmod : 80 % 7 = f % 7) (hne : f ≠ 10) :
    f ≤ 39 ∧ ∃ q : ℕ, q.Prime ∧ 11 ≤ q ∧ Nat.Coprime 7 q ∧ ¬ q ∣ 7 - 1 ∧
      q ∣ f.descFactorial 5 := by
  have hf : f = 17 ∨ f = 24 ∨ f = 31 ∨ f = 38 := by omega
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨by decide,13,by decide,by decide,by decide,by decide,by norm_num [Nat.descFactorial]⟩
  · exact ⟨by decide,23,by decide,by decide,by decide,by decide,by norm_num [Nat.descFactorial]⟩
  · exact ⟨by decide,31,by decide,by decide,by decide,by decide,by norm_num [Nat.descFactorial]⟩
  · exact ⟨by decide,37,by decide,by decide,by decide,by decide,by norm_num [Nat.descFactorial]⟩

end FiveTransitive.Degree80SevenArithmetic

end CFSG
