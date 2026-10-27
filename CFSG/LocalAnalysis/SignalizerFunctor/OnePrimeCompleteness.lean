module

public import CFSG.LocalAnalysis.SignalizerFunctor.CompletionCriterion
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeTransitivity

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem signalizer_common_fixed_compatible (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) :
    signalizerCompatible prime rank actor values (signalizerCommonFixed prime rank actor values) := by
  refine ⟨(Subgroup.le_centralizer_iff.mpr inf_le_left).trans
    (Subgroup.centralizer_le_normalizer _), ?_⟩
  intro subgroup member
  apply le_trans inf_le_left
  exact inf_le_right.trans ((iInf_le _ subgroup).trans (iInf_le _ member))

theorem conjugate_subgroup_eq_of_mem (element : GroupType) (target : Subgroup GroupType)
    (member : element ∈ target) : conjugateSubgroup element target = target :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer member)

theorem signalizer_one_prime_upper_bound [Finite GroupType]
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime) (distinct : prime ≠ groupPrime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (values_coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (values_invariant : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (values_pgroup : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      IsPGroup groupPrime (values subgroup)) :
    ∃ target : Subgroup GroupType, signalizerPrimeCompatible prime rank groupPrime actor values target ∧
      ∀ subgroup ∈ signalizerFunctorEk prime rank actor, values subgroup ≤ target := by
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ large
    rw [pow_add]
    exact Nat.le_mul_of_pos_right _ (pow_pos prime_prime.pos 2)
  obtain ⟨selected, selected_member⟩ := signalizerFunctorEk_nonempty prime rank prime_prime
    actor elementary rank_large
  have common_pgroup : IsPGroup groupPrime (signalizerCommonFixed prime rank actor values) :=
    (values_pgroup selected selected_member).to_le
      (inf_le_right.trans ((iInf_le _ selected).trans (iInf_le _ selected_member)))
  have common_compatible : signalizerPrimeCompatible prime rank groupPrime actor values
      (signalizerCommonFixed prime rank actor values) :=
    ⟨signalizer_common_fixed_compatible prime rank actor values, common_pgroup⟩
  obtain ⟨target, common_contains, target_maximal⟩ :=
    Finite.exists_le_maximal (p := signalizerPrimeCompatible prime rank groupPrime actor values)
      common_compatible
  refine ⟨target, target_maximal.prop, ?_⟩
  intro subgroup member
  have value_compatible : signalizerPrimeCompatible prime rank groupPrime actor values
      (values subgroup) := ⟨signalizer_value_compatible prime rank actor values
        values_invariant balanced member, values_pgroup subgroup member⟩
  obtain ⟨other, value_contains, other_maximal⟩ :=
    Finite.exists_le_maximal (p := signalizerPrimeCompatible prime rank groupPrime actor values)
      value_compatible
  obtain ⟨element, conjugates⟩ := signalizer_prime_transitivity prime rank groupPrime prime_prime
    groupPrime_prime distinct actor elementary large values values_coprime values_invariant
    balanced target other target_maximal other_maximal
  have equality := conjugate_subgroup_eq_of_mem element.val target
    (common_contains element.property)
  rw [equality] at conjugates
  rwa [← conjugates] at value_contains

theorem signalizer_one_prime_completeness [Finite GroupType]
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime) (distinct : prime ≠ groupPrime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (central : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      values subgroup ≤ Subgroup.centralizer (subgroup : Set GroupType))
    (values_coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (values_invariant : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (values_pgroup : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      IsPGroup groupPrime (values subgroup)) :
    let completion : Subgroup GroupType :=
      ⨆ subgroup ∈ signalizerFunctorEk prime rank actor, values subgroup
    (Nat.Coprime prime (Nat.card completion) ∧
      actor ≤ Subgroup.normalizer (completion : Set GroupType)) ∧
    (∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      completion ⊓ Subgroup.centralizer (subgroup : Set GroupType) = values subgroup) ∧
    (∀ target : Subgroup GroupType, actor ≤ Subgroup.normalizer (target : Set GroupType) →
      (∀ subgroup ∈ signalizerFunctorEk prime rank actor,
        target ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup) →
      target ≤ completion) ∧
    IsPGroup groupPrime completion ∧ Group.IsSolvable completion := by
  obtain ⟨target, compatible, contains⟩ := signalizer_one_prime_upper_bound prime rank groupPrime
    prime_prime groupPrime_prime distinct actor elementary large values values_coprime
    values_invariant balanced values_pgroup
  have bounds := centralizer_bounds_iff_exists_signalizer_upper_bound prime rank actor values
  have completion_bounds := bounds.mpr ⟨target, contains, compatible.1.2⟩
  have generation_large : prime ^ (rank + 1) ≤ Nat.card actor := by
    apply le_trans _ large
    rw [show rank + 2 = (rank + 1) + 1 by omega, pow_succ]
    exact Nat.le_mul_of_pos_right _ prime_prime.pos
  have properties := completion_properties_of_centralizer_bounds prime rank prime_prime actor
    elementary generation_large values central values_coprime values_invariant completion_bounds
  let completion : Subgroup GroupType :=
    ⨆ subgroup ∈ signalizerFunctorEk prime rank actor, values subgroup
  have completion_le : completion ≤ target := iSup_le fun subgroup => iSup_le (contains subgroup)
  have completion_pgroup := compatible.2.to_le completion_le
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  let _nilpotent : Group.IsNilpotent completion := completion_pgroup.isNilpotent
  exact ⟨properties.1, properties.2.1, properties.2.2, completion_pgroup, inferInstance⟩

end CFSG.SignalizerFunctor.Helpers
