module

public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientFixedFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerHyperplaneCores

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem embedded_prime_core_parent_normalized (parent : Subgroup GroupType) (primes : Set ℕ) :
    parent ≤ Subgroup.normalizer
      ((primeSetCore (GroupType := parent) primes).map parent.subtype : Set GroupType) := by
  let _characteristic := prime_set_core_characteristic (GroupType := parent) primes
  exact characteristic_subgroup_map_normalized parent parent Subgroup.le_normalizer
    (primeSetCore (GroupType := parent) primes)

theorem signalizer_hyperplane_local_product
    (prime rank groupPrime : ℕ) (actor hyperplane completion source : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (central : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected ≤ Subgroup.centralizer (selected : Set GroupType))
    (compatible : signalizerCompatible prime rank actor values completion)
    (core_le : signalizerHyperplaneCore prime rank groupPrime actor hyperplane values ≤ completion)
    (local_factorization : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected =
        (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ⊔
          (values selected ⊓ source))
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor)
    (contained : selected ≤ hyperplane) :
    ∀ element ∈ completion ⊓ Subgroup.centralizer (selected : Set GroupType),
      ∃ firstElement ∈ signalizerHyperplaneCore prime rank groupPrime actor hyperplane values ⊓
          Subgroup.centralizer (selected : Set GroupType),
        ∃ secondElement ∈ (completion ⊓ source) ⊓ Subgroup.centralizer (selected : Set GroupType),
          firstElement * secondElement = element := by
  intro element element_member
  let value := values selected
  let core := (primeSetCore (GroupType := value) ({groupPrime}ᶜ)).map value.subtype
  have value_member : element ∈ value := compatible.2 selected member element_member
  have decomposable : element ∈ core ⊔ (value ⊓ source) := by
    rw [← local_factorization selected member]
    exact value_member
  have normalizes : value ⊓ source ≤ Subgroup.normalizer (core : Set GroupType) :=
    inf_le_left.trans (embedded_prime_core_parent_normalized value ({groupPrime}ᶜ))
  obtain ⟨firstElement, first_member, secondElement, second_member, product⟩ :=
    (mem_sup_of_normalizing core (value ⊓ source) normalizes element).mp decomposable
  have first_value : firstElement ∈ value := (Subgroup.map_subtype_le _) first_member
  have first_core : firstElement ∈ signalizerHyperplaneCore prime rank groupPrime actor hyperplane values :=
    signalizer_hyperplane_core_contains prime rank groupPrime actor hyperplane values selected member contained first_member
  have first_completion := core_le first_core
  have second_completion : secondElement ∈ completion := by
    have cancelled := completion.mul_mem (completion.inv_mem first_completion) element_member.1
    rw [← product, ← mul_assoc, inv_mul_cancel, one_mul] at cancelled
    exact cancelled
  exact ⟨firstElement, ⟨first_core, central selected member first_value⟩,
    secondElement, ⟨⟨second_completion, second_member.2⟩, central selected member second_member.1⟩, product⟩

theorem signalizer_hyperplane_core_splitting
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor hyperplane source : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (hyperplane_le : hyperplane ≤ actor) (hyperplane_index : (hyperplane.subgroupOf actor).index = prime)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values)
    (source_normalized : actor ≤ Subgroup.normalizer (source : Set GroupType))
    (local_factorization : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected =
        (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ⊔
          (values selected ⊓ source)) :
    let completion := signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime})
    subgroupProduct (signalizerHyperplaneCore prime rank groupPrime actor hyperplane values)
      (completion ⊓ source) = (completion : Set GroupType) := by
  let completion := signalizerPrimeCompletion prime rank actor values
    (signalizerSpectrum prime rank actor values \ {groupPrime})
  let core := signalizerHyperplaneCore prime rank groupPrime actor hyperplane values
  have rank_bound : prime ^ (rank + 1) ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (by omega : rank + 1 ≤ rank + 2)).trans large
  have prime_complete := (locally_complete.2 groupPrime prime_member).1
  have control := signalizer_prime_completion_control prime rank prime_prime actor elementary rank_bound
    values conditions (signalizerSpectrum prime rank actor values \ {groupPrime}) prime_complete
  have properties := signalizer_hyperplane_core_properties prime rank groupPrime prime_prime groupPrime_prime
    actor hyperplane elementary rank_bound values conditions locally_complete prime_member
  have completion_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    ((pow_le_pow_right' prime_prime.one_le (Nat.le_succ rank)).trans rank_bound) values conditions.coprime
    completion control.1.1 control.1.2
  have hyperplane_bound := elementary_hyperplane_rank_bound prime rank prime_prime actor hyperplane
    hyperplane_le large hyperplane_index
  have completion_fixed_normalized : completion ⊓ Subgroup.centralizer (hyperplane : Set GroupType) ≤
      Subgroup.normalizer (core : Set GroupType) :=
    (signalizer_compatible_hyperplane_fixed_le prime rank actor hyperplane completion values control.1).trans
      properties.2.2
  apply ambient_order_fixed_factorization prime rank prime_prime hyperplane completion core
    (completion ⊓ source) (elementary_abelian_of_le prime elementary hyperplane_le) hyperplane_bound
    (hyperplane_le.trans control.1.1) completion_coprime properties.1 inf_le_left
    (hyperplane_le.trans properties.2.1)
    (normalizer_inf_of_le hyperplane completion source (hyperplane_le.trans control.1.1)
      (hyperplane_le.trans source_normalized)) completion_fixed_normalized
  intro selected member
  have actor_member : selected ∈ signalizerFunctorEk prime rank actor :=
    ⟨member.1.trans hyperplane_le, member.2⟩
  exact signalizer_hyperplane_local_product prime rank groupPrime actor hyperplane completion source values
    conditions.central control.1 properties.1 local_factorization selected actor_member member.1

end CFSG.SignalizerFunctor.Helpers
