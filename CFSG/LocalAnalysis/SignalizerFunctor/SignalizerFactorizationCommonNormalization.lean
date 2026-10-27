module

public import CFSG.LocalAnalysis.SignalizerFunctor.AbelianHallProductCompleteness

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem signalizer_factorization_common_normalizes_product
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime)
    (actor source factor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values)
    (source_normalized : actor ≤ Subgroup.normalizer (source : Set GroupType))
    (source_normalizes : source ≤ Subgroup.normalizer (factor : Set GroupType))
    (local_factorization : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected =
        (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ⊔
          (values selected ⊓ source)) :
    signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer
      (((signalizerPrimeCompletion prime rank actor values
        (signalizerSpectrum prime rank actor values \ {groupPrime})) ⊔ factor : Subgroup GroupType) :
          Set GroupType) := by
  have rank_large : prime ^ rank ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (Nat.le_succ rank)).trans large
  obtain ⟨selected, member⟩ := signalizerFunctorEk_nonempty prime rank prime_prime actor elementary rank_large
  let value := values selected
  let core := (primeSetCore (GroupType := value) ({groupPrime}ᶜ)).map value.subtype
  let complement := signalizerPrimeCompletion prime rank actor values
    (signalizerSpectrum prime rank actor values \ {groupPrime})
  have control := locally_complete_prime_deleted_control prime rank prime_prime actor elementary large
    values conditions locally_complete groupPrime prime_member
  have core_le := signalizer_local_complement_core_le_prime_completion prime rank groupPrime prime_prime
    (show groupPrime.Prime from prime_member.1) actor elementary large values conditions
    (locally_complete.2 groupPrime prime_member).1 selected member
  let _characteristic := prime_set_core_characteristic (GroupType := value) ({groupPrime}ᶜ)
  have core_normalized := characteristic_subgroup_map_normalized actor value
    (conditions.normalized selected member) (primeSetCore (GroupType := value) ({groupPrime}ᶜ))
  have value_normalizes_core := characteristic_subgroup_map_normalized value value Subgroup.le_normalizer
    (primeSetCore (GroupType := value) ({groupPrime}ᶜ))
  have whole : subgroupProduct core (value ⊓ source) = (value : Set GroupType) := by
    have factorization : value = core ⊔ (value ⊓ source) := local_factorization selected member
    ext element
    change (∃ first ∈ core, ∃ second ∈ value ⊓ source, first * second = element) ↔ element ∈ value
    rw [← mem_sup_of_normalizing core (value ⊓ source) (inf_le_left.trans value_normalizes_core) element,
      ← factorization]
  have fixed_product := normalized_product_fixed_points prime prime_prime actor value core (value ⊓ source)
    (elementary_abelian_isPGroup prime actor elementary) (conditions.normalized selected member)
    core_normalized (normalizer_inf_of_le actor value source (conditions.normalized selected member)
      source_normalized) (Subgroup.map_subtype_le _) inf_le_left (conditions.coprime selected member) whole
  rw [signalizer_value_common_fixed prime rank actor values conditions.balanced member] at fixed_product
  intro element element_member
  have decomposition : element ∈ subgroupProduct (core ⊓ Subgroup.centralizer (actor : Set GroupType))
      ((value ⊓ source) ⊓ Subgroup.centralizer (actor : Set GroupType)) := by
    rw [fixed_product]
    exact element_member
  obtain ⟨first, first_member, second, second_member, rfl⟩ := decomposition
  apply (Subgroup.normalizer _).mul_mem
  · exact Subgroup.le_normalizer ((show complement ≤ complement ⊔ factor from le_sup_left)
      (core_le first_member.1))
  · have second_common : second ∈ signalizerCommonFixed prime rank actor values := by
      rw [← signalizer_value_common_fixed prime rank actor values conditions.balanced member]
      exact ⟨second_member.1.1, second_member.2⟩
    exact Subgroup.inf_normalizer_le_normalizer_sup complement factor
      ⟨control.2.2.1 second_common, source_normalizes second_member.1.2⟩

end CFSG.SignalizerFunctor.Helpers
