module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSubfunctorValues
public import CFSG.LocalAnalysis.SignalizerFunctor.CentralizerImages

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem invariant_subgroup_map_normalized (actor target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (internal : Subgroup target)
    (invariant : let _action := conjugationAction actor target normalized
      ∀ actorElement : actor, ∀ element ∈ internal, actorElement • element ∈ internal) :
    actor ≤ Subgroup.normalizer (internal.map target.subtype : Set GroupType) := by
  let _action := conjugationAction actor target normalized
  apply Subgroup.le_normalizer_iff.mpr
  intro actorElement actor_member element member
  obtain ⟨representative, representative_member, rfl⟩ := member
  exact ⟨(⟨actorElement, actor_member⟩ : actor) • representative,
    invariant ⟨actorElement, actor_member⟩ representative representative_member, rfl⟩

theorem signalizer_prime_value_eq_fixed_hull [Finite GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ)
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor)
    (coprime : Nat.Coprime prime (Nat.card (values selected)))
    (normalized : actor ≤ Subgroup.normalizer (values selected : Set GroupType))
    (solvable : Group.IsSolvable (values selected)) :
    let _action := conjugationAction actor (values selected) normalized
    signalizerPrimeValue prime rank actor values primes selected =
      (fixedNormalizedPrimeHull (ActorType := actor) (GroupType := values selected) primes).map
        (values selected).subtype := by
  let target := values selected
  let := solvable
  let _action := conjugationAction actor target normalized
  let hull := fixedNormalizedPrimeHull (ActorType := actor) (GroupType := target) primes
  change signalizerPrimeValue prime rank actor values primes selected = hull.map target.subtype
  have hull_properties := fixed_normalized_prime_hull_properties prime prime_prime
    (elementary_abelian_isPGroup prime actor elementary) coprime primes
  have fixed_equal := signalizer_value_common_fixed prime rank actor values balanced member
  apply le_antisymm
  · apply iSup_le
    intro candidate
    apply iSup_le
    intro property
    have internal_supported : primeSupported primes (Nat.card (candidate.subgroupOf target)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe property.1).toEquiv]
      exact property.2.1
    have internal_le := fixed_normalized_prime_hull_contains primes (candidate.subgroupOf target)
      internal_supported
      (normalized_subgroupOf_invariant actor target candidate normalized property.2.2.1)
      (normalized_subgroupOf_fixed_normalized actor target candidate _ normalized
        (le_of_eq fixed_equal) property.2.2.2)
    have mapped_le := Subgroup.map_mono (f := target.subtype) internal_le
    rwa [Subgroup.map_subgroupOf_eq_of_le property.1] at mapped_le
  · have mapped_supported : primeSupported primes (Nat.card (hull.map target.subtype)) := by
      rw [Subgroup.card_map_of_injective target.subtype_injective]
      exact hull_properties.1
    have mapped_normalized := invariant_subgroup_map_normalized actor target normalized hull
      hull_properties.2.1
    have fixed_normalizes := normalizer_image_le target.subtype
      (FixedPoints.subgroup actor target) hull hull_properties.2.2
    rw [conjugation_fixed_subgroup_map actor target normalized] at fixed_normalizes
    have common_normalizes : signalizerCommonFixed prime rank actor values ≤
        Subgroup.normalizer (hull.map target.subtype : Set GroupType) := by
      rw [← fixed_equal]
      exact fixed_normalizes
    exact signalizer_prime_value_contains prime rank actor values primes selected
      (hull.map target.subtype) (Subgroup.map_subtype_le hull) mapped_supported mapped_normalized
      common_normalizes

end CFSG.SignalizerFunctor.Helpers
