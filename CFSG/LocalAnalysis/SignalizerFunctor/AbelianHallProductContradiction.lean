module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductComplementPrimeCollapse
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoPrimeOrderSolvability

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_contradiction
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (complement_eq : complement = signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime})) : False := by
  obtain ⟨complementPrime, complement_prime, _distinct, complement_pgroup⟩ :=
    incomplete_abelian_hall_product_complement_pgroup datum abelian large common_le_parent complement_eq
  have supported : ∀ divisor : ℕ, divisor.Prime → divisor ∣ Nat.card parent →
      divisor = groupPrime ∨ divisor = complementPrime := by
    intro divisor divisor_prime divides
    have cardinality := subgroup_product_cardinality complement factor
    rw [datum.whole] at cardinality
    have product_divides : divisor ∣ Nat.card complement * Nat.card factor := by
      rw [cardinality]
      exact dvd_mul_of_dvd_left divides _
    rcases divisor_prime.dvd_mul.mp product_divides with complement_divides | factor_divides
    · right
      let : Fact complementPrime.Prime := ⟨complement_prime⟩
      obtain ⟨exponent, power⟩ := IsPGroup.iff_card.mp complement_pgroup
      rw [power] at complement_divides
      have prime_divides := divisor_prime.dvd_of_dvd_pow complement_divides
      exact (Nat.prime_dvd_prime_iff_eq divisor_prime complement_prime).mp prime_divides
    · left
      let : Fact groupPrime.Prime := ⟨datum.groupPrime_prime⟩
      obtain ⟨exponent, power⟩ := IsPGroup.iff_card.mp datum.factor_pgroup
      rw [power] at factor_divides
      have prime_divides := divisor_prime.dvd_of_dvd_pow factor_divides
      exact (Nat.prime_dvd_prime_iff_eq divisor_prime datum.groupPrime_prime).mp prime_divides
  have solvable := two_prime_order_solvable parent groupPrime complementPrime datum.groupPrime_prime complement_prime supported
  exact datum.incomplete ⟨incomplete_hall_product_normalized_compatible parent datum le_rfl datum.parent_normalized, solvable⟩

end CFSG.SignalizerFunctor.Helpers
