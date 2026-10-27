module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedNormalizedPrimeHull

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def signalizerPrimeValue (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ)
    (selected : Subgroup GroupType) : Subgroup GroupType :=
  ⨆ (candidate : Subgroup GroupType)
    (_ : candidate ≤ values selected ∧ primeSupported primes (Nat.card candidate) ∧
      actor ≤ Subgroup.normalizer (candidate : Set GroupType) ∧
      signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (candidate : Set GroupType)),
    candidate

theorem signalizer_prime_value_contains (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ)
    (selected candidate : Subgroup GroupType)
    (contained : candidate ≤ values selected)
    (supported : primeSupported primes (Nat.card candidate))
    (normalized : actor ≤ Subgroup.normalizer (candidate : Set GroupType))
    (common_normalized : signalizerCommonFixed prime rank actor values ≤
      Subgroup.normalizer (candidate : Set GroupType)) :
    candidate ≤ signalizerPrimeValue prime rank actor values primes selected :=
  le_iSup_of_le candidate (le_iSup_of_le ⟨contained, supported, normalized, common_normalized⟩ le_rfl)

theorem signalizer_prime_value_le (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ)
    (selected : Subgroup GroupType) :
    signalizerPrimeValue prime rank actor values primes selected ≤ values selected := by
  apply iSup_le
  intro candidate
  apply iSup_le
  intro property
  exact property.1

theorem signalizer_prime_value_normalized (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ)
    (selected : Subgroup GroupType) :
    actor ≤ Subgroup.normalizer
      (signalizerPrimeValue prime rank actor values primes selected : Set GroupType) ∧
    signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer
      (signalizerPrimeValue prime rank actor values primes selected : Set GroupType) := by
  constructor
  · apply normalizer_iSup_of_le
    intro candidate
    apply normalizer_iSup_of_le
    intro property
    exact property.2.2.1
  · apply normalizer_iSup_of_le
    intro candidate
    apply normalizer_iSup_of_le
    intro property
    exact property.2.2.2

theorem normalized_subgroupOf_invariant (actor target subgroup : Subgroup GroupType)
    (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (subgroup_normalized : actor ≤ Subgroup.normalizer (subgroup : Set GroupType)) :
    let _action := conjugationAction actor target target_normalized
    ∀ actorElement : actor, ∀ element ∈ subgroup.subgroupOf target,
      actorElement • element ∈ subgroup.subgroupOf target := by
  let _action := conjugationAction actor target target_normalized
  change ∀ actorElement : actor, ∀ element ∈ subgroup.subgroupOf target,
    actorElement • element ∈ subgroup.subgroupOf target
  intro actorElement element member
  exact Subgroup.le_normalizer_iff.mp subgroup_normalized actorElement.val actorElement.property
    element.val member

theorem normalized_subgroupOf_fixed_normalized (actor target subgroup common : Subgroup GroupType)
    (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (fixed_le : target ⊓ Subgroup.centralizer (actor : Set GroupType) ≤ common)
    (common_normalized : common ≤ Subgroup.normalizer (subgroup : Set GroupType)) :
    let _action := conjugationAction actor target target_normalized
    FixedPoints.subgroup actor target ≤ Subgroup.normalizer
      (subgroup.subgroupOf target : Set target) := by
  let _action := conjugationAction actor target target_normalized
  change FixedPoints.subgroup actor target ≤ Subgroup.normalizer
    (subgroup.subgroupOf target : Set target)
  intro element fixed
  have ambient_fixed : element.val ∈ target ⊓ Subgroup.centralizer (actor : Set GroupType) := by
    rw [← conjugation_fixed_subgroup_map actor target target_normalized]
    exact Subgroup.mem_map_of_mem target.subtype fixed
  have ambient_normalizes := common_normalized (fixed_le ambient_fixed)
  apply Subgroup.mem_normalizer_iff.mpr
  intro representative
  exact Subgroup.mem_normalizer_iff.mp ambient_normalizes representative.val

theorem signalizer_prime_value_supported [Finite GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ)
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (selected : Subgroup GroupType)
    (selected_member : selected ∈ signalizerFunctorEk prime rank actor)
    (coprime : Nat.Coprime prime (Nat.card (values selected)))
    (normalized : actor ≤ Subgroup.normalizer (values selected : Set GroupType))
    (solvable : Group.IsSolvable (values selected)) :
    primeSupported primes (Nat.card (signalizerPrimeValue prime rank actor values primes selected)) := by
  let target := values selected
  let := solvable
  let _action := conjugationAction actor target normalized
  let hull := fixedNormalizedPrimeHull (ActorType := actor) (GroupType := target) primes
  have hull_properties := fixed_normalized_prime_hull_properties prime prime_prime
    (elementary_abelian_isPGroup prime actor elementary) coprime primes
  have primeValue_le : signalizerPrimeValue prime rank actor values primes selected ≤
      hull.map target.subtype := by
    apply iSup_le
    intro candidate
    apply iSup_le
    intro property
    have internal_supported : primeSupported primes (Nat.card (candidate.subgroupOf target)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe property.1).toEquiv]
      exact property.2.1
    have internal_invariant := normalized_subgroupOf_invariant actor target candidate normalized
      property.2.2.1
    have internal_fixed_normalized := normalized_subgroupOf_fixed_normalized actor target candidate
      (signalizerCommonFixed prime rank actor values) normalized
      (le_of_eq (signalizer_value_common_fixed prime rank actor values balanced selected_member))
      property.2.2.2
    have internal_le := fixed_normalized_prime_hull_contains primes (candidate.subgroupOf target)
      internal_supported internal_invariant internal_fixed_normalized
    have mapped_le := Subgroup.map_mono (f := target.subtype) internal_le
    rwa [Subgroup.map_subgroupOf_eq_of_le property.1] at mapped_le
  have mapped_supported : primeSupported primes (Nat.card (hull.map target.subtype)) := by
    rw [Subgroup.card_map_of_injective target.subtype_injective]
    exact hull_properties.1
  exact prime_supported_of_dvd primes mapped_supported (Subgroup.card_dvd_of_le primeValue_le)

end CFSG.SignalizerFunctor.Helpers
