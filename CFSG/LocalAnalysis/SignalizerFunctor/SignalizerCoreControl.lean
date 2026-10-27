module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeCompletionControl
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableCompatibility
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalPrimeSupplements
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem signalizer_local_complement_core_le_prime_completion
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (complete : signalizerCompatible prime rank actor
      (signalizerPrimeValue prime rank actor values (signalizerSpectrum prime rank actor values \ {groupPrime}))
      (⨆ selected ∈ signalizerFunctorEk prime rank actor,
        signalizerPrimeValue prime rank actor values
          (signalizerSpectrum prime rank actor values \ {groupPrime}) selected))
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor) :
    (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ≤
      ⨆ selected ∈ signalizerFunctorEk prime rank actor,
        signalizerPrimeValue prime rank actor values
          (signalizerSpectrum prime rank actor values \ {groupPrime}) selected := by
  let target := values selected
  let internalCore := primeSetCore (GroupType := target) ({groupPrime}ᶜ)
  let core := internalCore.map target.subtype
  let _characteristic := prime_set_core_characteristic (GroupType := target) ({groupPrime}ᶜ)
  have actor_normalized := characteristic_subgroup_map_normalized actor target
    (conditions.normalized selected member) internalCore
  have common_le : signalizerCommonFixed prime rank actor values ≤ target := by
    rw [← signalizer_value_common_fixed prime rank actor values conditions.balanced member]
    exact inf_le_left
  have common_normalized := characteristic_subgroup_map_normalized _ target
    (common_le.trans Subgroup.le_normalizer) internalCore
  have compatible := solvable_signalizer_compatible_of_le prime rank actor values target core
    (solvable_signalizer_value_compatible prime rank actor values conditions selected member)
    (Subgroup.map_subtype_le internalCore) actor_normalized
  have core_supported : primeSupported (signalizerSpectrum prime rank actor values \ {groupPrime})
      (Nat.card core) := by
    intro divisor divisor_prime divides
    refine ⟨⟨divisor_prime, selected, member,
      divides.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le internalCore))⟩, ?_⟩
    have core_coprime : Nat.Coprime groupPrime (Nat.card core) := by
      rw [Subgroup.card_map_of_injective target.subtype_injective]
      exact (prime_supported_complement_singleton_iff_coprime groupPrime groupPrime_prime _).mp
        (prime_set_core_supported ({groupPrime}ᶜ))
    intro equality
    have equal : divisor = groupPrime := equality
    subst divisor
    exact groupPrime_prime.coprime_iff_not_dvd.mp core_coprime divides
  exact (signalizer_prime_completion_control prime rank prime_prime actor elementary large values
    conditions _ complete).2.2.2 core compatible.1 core_supported common_normalized

theorem normalized_prime_subgroup_center_nontrivial
    (groupPrime : ℕ) (groupPrime_prime : groupPrime.Prime)
    (actor target : Subgroup GroupType) (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (pgroup : IsPGroup groupPrime target) (nontrivial : target ≠ ⊥) :
    let center := (Subgroup.center target).map target.subtype
    center ≠ ⊥ ∧ IsMulCommutative center ∧ IsPGroup groupPrime center ∧
      actor ≤ Subgroup.normalizer (center : Set GroupType) := by
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  let _targetNontrivial : Nontrivial target := (Subgroup.nontrivial_iff_ne_bot target).mpr nontrivial
  let _centerNontrivial := pgroup.center_nontrivial
  let center := (Subgroup.center target).map target.subtype
  have center_nontrivial : center ≠ ⊥ := by
    intro trivial
    have internal_trivial := (Subgroup.map_eq_bot_iff_of_injective _ target.subtype_injective).mp trivial
    exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center target)).mp inferInstance internal_trivial
  exact ⟨center_nontrivial, inferInstance, (pgroup.to_subgroup _).map target.subtype,
    characteristic_subgroup_map_normalized actor target normalized (Subgroup.center target)⟩

theorem normal_prime_subgroup_le_ambient_supplement
    (groupPrime : ℕ) (groupPrime_prime : groupPrime.Prime)
    (parent normal supplement : Subgroup GroupType) (normal_le : normal ≤ parent)
    (normal_internal : (normal.subgroupOf parent).Normal)
    (normal_pgroup : IsPGroup groupPrime normal)
    (whole : parent =
      (primeSetCore (GroupType := parent) ({groupPrime}ᶜ)).map parent.subtype ⊔ (parent ⊓ supplement)) :
    normal ≤ supplement := by
  let internalCore := primeSetCore (GroupType := parent) ({groupPrime}ᶜ)
  let _normalCore := prime_set_core_normal (GroupType := parent) ({groupPrime}ᶜ)
  let := normal_internal
  have internal_pgroup : IsPGroup groupPrime (normal.subgroupOf parent) :=
    normal_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe normal_le).symm
  have internal_whole : internalCore ⊔ supplement.subgroupOf parent = ⊤ := by
    apply (Subgroup.map_injective parent.subtype_injective)
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
      parent.subtype_range, inf_comm]
    exact whole.symm
  have internal_contained := normal_prime_subgroup_le_supplement groupPrime groupPrime_prime
    internalCore (supplement.subgroupOf parent) (normal.subgroupOf parent)
    ((prime_supported_complement_singleton_iff_coprime groupPrime groupPrime_prime _).mp
      (prime_set_core_supported ({groupPrime}ᶜ))) internal_whole internal_pgroup
  have mapped_contained := Subgroup.map_mono (f := parent.subtype) internal_contained
  rw [Subgroup.map_subgroupOf_eq_of_le normal_le, Subgroup.subgroupOf_map_subtype] at mapped_contained
  exact mapped_contained.trans inf_le_left

end CFSG.SignalizerFunctor.Helpers
