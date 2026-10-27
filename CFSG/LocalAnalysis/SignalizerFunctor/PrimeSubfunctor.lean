module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSubfunctorValues

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem signalizer_prime_subfunctor_properties
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ)
    (central : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      values subgroup ≤ Subgroup.centralizer (subgroup : Set GroupType))
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (normalized : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (solvable : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Group.IsSolvable (values subgroup)) :
    let primeValues := signalizerPrimeValue prime rank actor values primes
    (∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      primeValues subgroup ≤ Subgroup.centralizer (subgroup : Set GroupType) ∧
      Nat.Coprime prime (Nat.card (primeValues subgroup)) ∧
      actor ≤ Subgroup.normalizer (primeValues subgroup : Set GroupType) ∧
      Group.IsSolvable (primeValues subgroup) ∧
      primeSupported primes (Nat.card (primeValues subgroup))) ∧
    (∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        primeValues subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ primeValues other) := by
  let primeValues := signalizerPrimeValue prime rank actor values primes
  have values_supported : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      primeSupported primes (Nat.card (primeValues subgroup)) := by
    intro subgroup member
    exact signalizer_prime_value_supported prime rank prime_prime actor elementary values primes
      balanced subgroup member (coprime subgroup member) (normalized subgroup member)
      (solvable subgroup member)
  refine ⟨?_, ?_⟩
  · intro subgroup member
    have contained := signalizer_prime_value_le prime rank actor values primes subgroup
    let := solvable subgroup member
    have primeValue_solvable : Group.IsSolvable (primeValues subgroup) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective contained)
    exact ⟨contained.trans (central subgroup member),
      (coprime subgroup member).of_dvd_right (Subgroup.card_dvd_of_le contained),
      (signalizer_prime_value_normalized prime rank actor values primes subgroup).1,
      primeValue_solvable, values_supported subgroup member⟩
  · intro subgroup member other other_member
    let candidate := primeValues subgroup ⊓ Subgroup.centralizer (other : Set GroupType)
    have candidate_le : candidate ≤ values other :=
      (inf_le_inf_right _ (signalizer_prime_value_le prime rank actor values primes subgroup)).trans
        (balanced subgroup member other other_member)
    have candidate_supported : primeSupported primes (Nat.card candidate) :=
      prime_supported_of_dvd primes (values_supported subgroup member)
        (Subgroup.card_dvd_of_le inf_le_left)
    have candidate_normalized : actor ≤ Subgroup.normalizer (candidate : Set GroupType) :=
      normalizer_inf_of_le actor _ _
        (signalizer_prime_value_normalized prime rank actor values primes subgroup).1
        ((elementary_abelian_le_centralizer prime actor other elementary other_member.1).trans
          Subgroup.le_normalizer)
    have common_centralizes : signalizerCommonFixed prime rank actor values ≤
        Subgroup.centralizer (other : Set GroupType) :=
      inf_le_left.trans (Subgroup.centralizer_le other_member.1)
    have common_normalized : signalizerCommonFixed prime rank actor values ≤
        Subgroup.normalizer (candidate : Set GroupType) :=
      normalizer_inf_of_le _ _ _
        (signalizer_prime_value_normalized prime rank actor values primes subgroup).2
        (common_centralizes.trans Subgroup.le_normalizer)
    exact signalizer_prime_value_contains prime rank actor values primes other candidate
      candidate_le candidate_supported candidate_normalized common_normalized

omit [Finite GroupType] in
theorem signalizer_prime_subfunctor_dominates
    (prime rank : ℕ) (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ)
    (target : Subgroup GroupType)
    (compatible : signalizerCompatible prime rank actor values target)
    (supported : primeSupported primes (Nat.card target))
    (common_normalized : signalizerCommonFixed prime rank actor values ≤
      Subgroup.normalizer (target : Set GroupType)) :
    signalizerCompatible prime rank actor (signalizerPrimeValue prime rank actor values primes)
      target := by
  refine ⟨compatible.1, ?_⟩
  intro subgroup member
  let candidate := target ⊓ Subgroup.centralizer (subgroup : Set GroupType)
  have candidate_normalized : actor ≤ Subgroup.normalizer (candidate : Set GroupType) :=
    normalizer_inf_of_le actor _ _ compatible.1
      ((elementary_abelian_le_centralizer prime actor subgroup elementary member.1).trans
        Subgroup.le_normalizer)
  have common_centralizes : signalizerCommonFixed prime rank actor values ≤
      Subgroup.centralizer (subgroup : Set GroupType) :=
    inf_le_left.trans (Subgroup.centralizer_le member.1)
  have candidate_common_normalized : signalizerCommonFixed prime rank actor values ≤
      Subgroup.normalizer (candidate : Set GroupType) :=
    normalizer_inf_of_le _ _ _ common_normalized (common_centralizes.trans Subgroup.le_normalizer)
  exact signalizer_prime_value_contains prime rank actor values primes subgroup candidate
    (compatible.2 subgroup member)
    (prime_supported_of_dvd primes supported (Subgroup.card_dvd_of_le inf_le_left))
    candidate_normalized candidate_common_normalized

end CFSG.SignalizerFunctor.Helpers
