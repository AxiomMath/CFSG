module

public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG

namespace FiveTransitive.Degree72FactorizationArithmetic

theorem factor_exponents {h : ℕ} (hh : h ≠ 0)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ h → p = 2 ∨ p = 5 ∨ p = 11) :
    h = 2 ^ h.factorization 2 * 5 ^ h.factorization 5 * 11 ^ h.factorization 11 := by
  apply Nat.eq_of_factorization_eq hh (by positivity)
  intro p
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply,Nat.factorization_pow,Finsupp.smul_apply]
  by_cases h2 : p = 2
  · subst p
    norm_num [Nat.prime_two.factorization,(show Nat.Prime 5 by decide).factorization,
      (show Nat.Prime 11 by decide).factorization]
  by_cases h5 : p = 5
  · subst p
    norm_num [Nat.prime_two.factorization,(show Nat.Prime 5 by decide).factorization,
      (show Nat.Prime 11 by decide).factorization]
  by_cases h11 : p = 11
  · subst p
    norm_num [Nat.prime_two.factorization,(show Nat.Prime 5 by decide).factorization,
      (show Nat.Prime 11 by decide).factorization]
  have hz : h.factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    by_cases hp : p.Prime
    · exact Or.inr (Or.inl (fun hd => by rcases hprime p hp hd with h | h | h <;> contradiction))
    · exact Or.inl hp
  simp [hz,Nat.prime_two.factorization,(show Nat.Prime 5 by decide).factorization,
    (show Nat.Prime 11 by decide).factorization,h2,h5,h11]

theorem factorial_two : (Nat.factorial 67).factorization 2 = 64 := by
  rw [Nat.factorization_factorial Nat.prime_two (b := 7) (by decide)]
  norm_num [Finset.sum_Ico_succ_top]

end FiveTransitive.Degree72FactorizationArithmetic

end CFSG
