module

public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree79LargePrimeArithmetic

theorem normalizer_prime
    (p f : ℕ)
    (hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37)
    (hlo : 5 ≤ f) (hhi : f ≤ 39) (hmod : 79 % p = f % p) :
    ∃ q : ℕ, q.Prime ∧ p.Coprime q ∧ ¬ q ∣ p - 1 ∧
      q ∣ f.descFactorial 5 ∧ 79 < p * q + f := by
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hf : f = 13 ∨ f = 24 ∨ f = 35 := by omega
    rcases hf with rfl | rfl | rfl
    · exact ⟨13,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
    · exact ⟨23,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
    · exact ⟨31,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 14 ∨ f = 27 := by omega
    rcases hf with rfl | rfl
    · exact ⟨11,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
    · exact ⟨23,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 11 ∨ f = 28 := by omega
    rcases hf with rfl | rfl
    · exact ⟨11,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
    · exact ⟨13,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 22 := by omega
    subst f
    exact ⟨7,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 10 ∨ f = 33 := by omega
    rcases hf with rfl | rfl
    · exact ⟨7,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
    · exact ⟨31,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 21 := by omega
    subst f
    exact ⟨19,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 17 := by omega
    subst f
    exact ⟨13,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩
  · have hf : f = 5 := by omega
    subst f
    exact ⟨5,by decide,by decide,by decide,by norm_num [Nat.descFactorial],by decide⟩

end FiveTransitive.Degree79LargePrimeArithmetic

end CFSG
