module

public import CFSG.LocalAnalysis.SignalizerFunctor.AbelianHallProductContradiction

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem locally_complete_prime_deleted_control
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (groupPrime : ℕ) (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values) :
    let primes := signalizerSpectrum prime rank actor values \ {groupPrime}
    let completion := signalizerPrimeCompletion prime rank actor values primes
    solvableSignalizerCompatible prime rank actor values completion ∧
      primeSupported primes (Nat.card completion) ∧
      signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (completion : Set GroupType) ∧
      (∀ target : Subgroup GroupType, signalizerCompatible prime rank actor values target →
        primeSupported primes (Nat.card target) →
        signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (target : Set GroupType) →
        target ≤ completion) := by
  have complete := locally_complete.2 groupPrime prime_member
  have control := signalizer_prime_completion_control prime rank prime_prime actor elementary large
    values conditions _ complete.1
  exact ⟨⟨control.1, complete.2⟩, control.2⟩

omit [Finite GroupType] in
theorem normalized_product_parent_properties (actor parent first second : Subgroup GroupType)
    (first_normalized : actor ≤ Subgroup.normalizer (first : Set GroupType))
    (second_normalized : actor ≤ Subgroup.normalizer (second : Set GroupType))
    (whole : subgroupProduct first second = (parent : Set GroupType)) :
    first ≤ parent ∧ second ≤ parent ∧ actor ≤ Subgroup.normalizer (parent : Set GroupType) := by
  have first_le : first ≤ parent := by
    intro element member
    have product_member : element ∈ subgroupProduct first second :=
      ⟨element, member, 1, second.one_mem, mul_one _⟩
    rwa [whole] at product_member
  have second_le : second ≤ parent := by
    intro element member
    have product_member : element ∈ subgroupProduct first second :=
      ⟨1, first.one_mem, element, member, one_mul _⟩
    rwa [whole] at product_member
  refine ⟨first_le, second_le, Subgroup.le_normalizer_iff.mpr ?_⟩
  intro actorElement actor_member element member
  have product_member : element ∈ subgroupProduct first second := by rwa [whole]
  obtain ⟨firstElement, first_member, secondElement, second_member, rfl⟩ := product_member
  have conjugate_member : actorElement * (firstElement * secondElement) * actorElement⁻¹ ∈
      subgroupProduct first second := by
    refine ⟨actorElement * firstElement * actorElement⁻¹,
      Subgroup.le_normalizer_iff.mp first_normalized actorElement actor_member firstElement first_member,
      actorElement * secondElement * actorElement⁻¹,
      Subgroup.le_normalizer_iff.mp second_normalized actorElement actor_member secondElement second_member, ?_⟩
    group
  rwa [whole] at conjugate_member

theorem abelian_hall_product_solvable_compatible
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor parent factor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values)
    (factor_compatible : signalizerCompatible prime rank actor values factor)
    (factor_pgroup : IsPGroup groupPrime factor) (abelian : IsMulCommutative factor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (whole : subgroupProduct
      (signalizerPrimeCompletion prime rank actor values
        (signalizerSpectrum prime rank actor values \ {groupPrime})) factor = (parent : Set GroupType)) :
    solvableSignalizerCompatible prime rank actor values parent := by
  have generation_large : prime ^ (rank + 1) ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (by omega : rank + 1 ≤ rank + 2)).trans large
  let complement := signalizerPrimeCompletion prime rank actor values
    (signalizerSpectrum prime rank actor values \ {groupPrime})
  have control := locally_complete_prime_deleted_control prime rank prime_prime actor elementary
    generation_large values conditions locally_complete groupPrime prime_member
  have complement_coprime : Nat.Coprime groupPrime (Nat.card complement) := by
    apply groupPrime_prime.coprime_iff_not_dvd.mpr
    intro divides
    exact (control.2.1 groupPrime groupPrime_prime divides).2 (Set.mem_singleton groupPrime)
  have properties := normalized_product_parent_properties actor parent complement factor
    control.1.1.1 factor_compatible.1 whole
  by_contra incomplete
  let datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values :=
    { prime_prime := prime_prime
      groupPrime_prime := groupPrime_prime
      elementary := elementary
      large := generation_large
      conditions := conditions
      parent_normalized := properties.2.2
      locally_complete := locally_complete
      incomplete := incomplete
      complement_compatible := control.1
      factor_compatible := factor_compatible
      complement_le := properties.1
      factor_le := properties.2.1
      complement_coprime := complement_coprime
      factor_pgroup := factor_pgroup
      whole := whole }
  exact incomplete_abelian_hall_product_contradiction datum abelian large common_le_parent rfl

theorem abelian_hall_product_complete
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor parent factor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values)
    (factor_compatible : signalizerCompatible prime rank actor values factor)
    (factor_pgroup : IsPGroup groupPrime factor) (abelian : IsMulCommutative factor)
    (values_le_parent : ∀ selected ∈ signalizerFunctorEk prime rank actor, values selected ≤ parent)
    (whole : subgroupProduct
      (signalizerPrimeCompletion prime rank actor values
        (signalizerSpectrum prime rank actor values \ {groupPrime})) factor = (parent : Set GroupType)) :
    (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) = parent ∧
      solvableSignalizerCompatible prime rank actor values parent := by
  have generation_large : prime ^ (rank + 1) ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (by omega : rank + 1 ≤ rank + 2)).trans large
  obtain ⟨selected, member⟩ := signalizerFunctorEk_nonempty prime rank prime_prime actor elementary
    ((pow_le_pow_right' prime_prime.one_le (by omega : rank ≤ rank + 2)).trans large)
  have common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent := by
    rw [← signalizer_value_common_fixed prime rank actor values conditions.balanced member]
    exact inf_le_left.trans (values_le_parent selected member)
  have compatible := abelian_hall_product_solvable_compatible prime rank groupPrime prime_prime
    groupPrime_prime actor parent factor elementary large values conditions locally_complete prime_member
    factor_compatible factor_pgroup abelian common_le_parent whole
  refine ⟨le_antisymm (iSup_le fun selected => iSup_le (values_le_parent selected)) ?_, compatible⟩
  exact signalizer_maximality prime rank prime_prime actor elementary generation_large values
    conditions.coprime parent compatible.1.1 compatible.1.2

end CFSG.SignalizerFunctor.Helpers
