module

public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree80LargePrimeArithmetic

theorem normalizer_prime
    (p f : ℕ)
    (hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37)
    (hlo : 5 ≤ f) (hhi : f ≤ 40) (hmod : 80 % p = f % p) :
    f ≤ 39 ∧ ∃ q : ℕ, q.Prime ∧ p.Coprime q ∧ ¬ q ∣ p - 1 ∧
      q ∣ f.descFactorial 5 ∧ 80 < p * q + f := by
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hf : f = 14 ∨ f = 25 ∨ f = 36 := by omega
    rcases hf with rfl | rfl | rfl
    · exact ⟨by decide,13,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
    · exact ⟨by decide,23,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
    · exact ⟨by decide,17,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 15 ∨ f = 28 := by omega
    rcases hf with rfl | rfl
    · exact ⟨by decide,11,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
    · exact ⟨by decide,7,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 12 ∨ f = 29 := by omega
    rcases hf with rfl | rfl
    · exact ⟨by decide,11,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
    · exact ⟨by decide,29,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 23 := by omega
    subst f
    exact ⟨by decide,23,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 11 ∨ f = 34 := by omega
    rcases hf with rfl | rfl
    · exact ⟨by decide,7,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
    · exact ⟨by decide,31,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 22 := by omega
    subst f
    exact ⟨by decide,19,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 18 := by omega
    subst f
    exact ⟨by decide,17,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 6 := by omega
    subst f
    exact ⟨by decide,5,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩

end FiveTransitive.Degree80LargePrimeArithmetic

end CFSG
