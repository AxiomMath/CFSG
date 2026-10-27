module

public import CFSG.Permutation.FiveTransitive.Degree36FiveFixerNumeric
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Nat.Factorization.Defs

public section

namespace CFSG

namespace FiveTransitive.Degree36SixCasesNumeric

open Degree36FiveFixerNumeric

theorem three_factorization (a b c : ℕ) :
    (2^a * 3^b * 5^c).factorization 3 = b := by
  have h2 : (2 : ℕ)^a ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (3 : ℕ)^b ≠ 0 := pow_ne_zero _ (by norm_num)
  have h5 : (5 : ℕ)^c ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Nat.factorization_mul (mul_ne_zero h2 h3) h5,Nat.factorization_mul h2 h3,
    Finsupp.add_apply,Finsupp.add_apply,Nat.factorization_pow,Nat.factorization_pow,
    Nat.factorization_pow,Finsupp.smul_apply,Finsupp.smul_apply,Finsupp.smul_apply]
  norm_num [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 5),
    (by norm_num : Nat.Prime 3).factorization]

theorem six_values {a b c : ℕ}
    (hm : (a,b,c) ∈ allowedTriplesFour)
    (hthree : 3^b = 1 ∨ 3^b = 3 ∨ 3^b = 81)
    (hfree : ¬ 9 ∣ 2^a * 3^b * 5^c → ¬ 5 ∣ 2^a * 3^b * 5^c) :
    2^a * 3^b * 5^c = 2 ∨ 2^a * 3^b * 5^c = 4 ∨
      2^a * 3^b * 5^c = 128 ∨ 2^a * 3^b * 5^c = 256 ∨
      2^a * 3^b * 5^c = 41472 ∨ 2^a * 3^b * 5^c = 82944 := by
  change (a,b,c) ∈ allowedTriples.filter (fun t => t.2.1 ≤ 4) at hm
  obtain ⟨hm,hb⟩ := Finset.mem_filter.mp hm
  change b ≤ 4 at hb
  simp only [allowedTriples,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at hm
  rcases hm with
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals norm_num at hb
  all_goals norm_num at hthree
  all_goals norm_num at hfree
  all_goals norm_num

end FiveTransitive.Degree36SixCasesNumeric

end CFSG
