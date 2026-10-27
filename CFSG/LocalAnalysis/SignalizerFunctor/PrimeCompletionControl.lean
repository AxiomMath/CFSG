module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSupport
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerConditions

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem signalizer_prime_completion_control
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values) (primes : Set ℕ)
    (complete : signalizerCompatible prime rank actor
      (signalizerPrimeValue prime rank actor values primes)
      (⨆ selected ∈ signalizerFunctorEk prime rank actor,
        signalizerPrimeValue prime rank actor values primes selected)) :
    let completion := ⨆ selected ∈ signalizerFunctorEk prime rank actor,
      signalizerPrimeValue prime rank actor values primes selected
    signalizerCompatible prime rank actor values completion ∧
      primeSupported primes (Nat.card completion) ∧
      signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (completion : Set GroupType) ∧
      (∀ target : Subgroup GroupType, signalizerCompatible prime rank actor values target →
        primeSupported primes (Nat.card target) →
        signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (target : Set GroupType) →
        target ≤ completion) := by
  let primeValues := signalizerPrimeValue prime rank actor values primes
  let completion := ⨆ selected ∈ signalizerFunctorEk prime rank actor, primeValues selected
  have prime_conditions := solvable_signalizer_prime_subfunctor_conditions prime rank prime_prime
    actor elementary values conditions primes
  have supported_values : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      primeSupported primes (Nat.card (primeValues selected)) := by
    intro selected member
    exact signalizer_prime_value_supported prime rank prime_prime actor elementary values primes
      conditions.balanced selected member (conditions.coprime selected member)
      (conditions.normalized selected member) (conditions.solvable selected member)
  refine ⟨⟨complete.1, fun selected member => (complete.2 selected member).trans
    (signalizer_prime_value_le prime rank actor values primes selected)⟩, ?_, ?_, ?_⟩
  · intro groupPrime groupPrime_prime divides
    obtain ⟨selected, member, value_divides⟩ := signalizer_compatible_prime_support prime rank groupPrime
      prime_prime groupPrime_prime actor elementary large primeValues prime_conditions.coprime
      completion complete divides
    exact supported_values selected member groupPrime groupPrime_prime value_divides
  · apply normalizer_biSup_of_le
    intro selected _
    exact (signalizer_prime_value_normalized prime rank actor values primes selected).2
  · intro target target_compatible target_supported common_normalized
    have prime_compatible := signalizer_prime_subfunctor_dominates prime rank actor elementary values
      primes target target_compatible target_supported common_normalized
    exact signalizer_maximality prime rank prime_prime actor elementary large primeValues
      prime_conditions.coprime target prime_compatible.1 prime_compatible.2

end CFSG.SignalizerFunctor.Helpers
