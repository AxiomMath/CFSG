module

public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree80FactorizationArithmetic

theorem factor_exponents {h : ℕ} (hh : h ≠ 0)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ h → p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7) :
    h = 2 ^ h.factorization 2 * 3 ^ h.factorization 3 *
      5 ^ h.factorization 5 * 7 ^ h.factorization 7 := by
  apply Nat.eq_of_factorization_eq hh (by positivity)
  intro p
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply,Nat.factorization_pow,Finsupp.smul_apply]
  by_cases h2 : p = 2
  · subst p
    norm_num [Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization,
      (show Nat.Prime 5 by decide).factorization,(show Nat.Prime 7 by decide).factorization]
  by_cases h3 : p = 3
  · subst p
    norm_num [Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization,
      (show Nat.Prime 5 by decide).factorization,(show Nat.Prime 7 by decide).factorization]
  by_cases h5 : p = 5
  · subst p
    norm_num [Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization,
      (show Nat.Prime 5 by decide).factorization,(show Nat.Prime 7 by decide).factorization]
  by_cases h7 : p = 7
  · subst p
    norm_num [Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization,
      (show Nat.Prime 5 by decide).factorization,(show Nat.Prime 7 by decide).factorization]
  have hz : h.factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    by_cases hp : p.Prime
    · exact Or.inr (Or.inl (fun hd => by rcases hprime p hp hd with h | h | h | h <;> contradiction))
    · exact Or.inl hp
  simp [hz,Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization,
    (show Nat.Prime 5 by decide).factorization,(show Nat.Prime 7 by decide).factorization,
    h2,h3,h5,h7]

end FiveTransitive.Degree80FactorizationArithmetic

end CFSG
