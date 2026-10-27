module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedGrowth
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantFusion

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem ambient_subgroup_fixed_eq_centralizer (actor : Subgroup GroupType)
    (subgroup : Subgroup actor) :
    let _action := ambientConjugationAction actor
    let _baseAction : MulAction actor GroupType := _action.toMulAction
    FixedPoints.subgroup subgroup GroupType =
      Subgroup.centralizer (subgroup.map actor.subtype : Set GroupType) := by
  let _action := ambientConjugationAction actor
  let _baseAction : MulAction actor GroupType := _action.toMulAction
  change FixedPoints.subgroup subgroup GroupType =
    Subgroup.centralizer (subgroup.map actor.subtype : Set GroupType)
  ext element
  constructor
  · intro fixed
    apply Subgroup.mem_centralizer_iff.mpr
    intro actorElement member
    obtain ⟨representative, representative_member, rfl⟩ := member
    have equality := fixed (⟨representative, representative_member⟩ : subgroup)
    change representative.val * element * representative.val⁻¹ = element at equality
    exact mul_inv_eq_iff_eq_mul.mp equality
  · intro central actorElement
    change actorElement.val.val * element * actorElement.val.val⁻¹ = element
    apply mul_inv_eq_iff_eq_mul.mpr
    exact Subgroup.mem_centralizer_iff.mp central actorElement.val.val
      (Subgroup.mem_map_of_mem actor.subtype actorElement.property)

theorem elementary_pair_normalizer_fixed_growth [Finite GroupType]
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime) (distinct : prime ≠ groupPrime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (first second : Subgroup GroupType)
    (first_pgroup : IsPGroup groupPrime first) (second_pgroup : IsPGroup groupPrime second)
    (first_normalized : actor ≤ Subgroup.normalizer (first : Set GroupType))
    (second_normalized : actor ≤ Subgroup.normalizer (second : Set GroupType))
    (first_proper : first ⊓ second < first) (second_proper : first ⊓ second < second) :
    ∃ subgroup ∈ signalizerFunctorEk prime rank actor,
      ¬ (first ⊓ Subgroup.normalizer (first ⊓ second : Set GroupType)) ⊓
        Subgroup.centralizer (subgroup : Set GroupType) ≤ first ⊓ second ∧
      ¬ (second ⊓ Subgroup.normalizer (first ⊓ second : Set GroupType)) ⊓
        Subgroup.centralizer (subgroup : Set GroupType) ≤ first ⊓ second := by
  let := elementary.1
  let _actorCommGroup : CommGroup actor := { actor.toGroup with mul_comm := mul_comm' }
  let _action := ambientConjugationAction actor
  let _baseAction : MulAction actor GroupType := _action.toMulAction
  let intersection := first ⊓ second
  let firstNormalizer := first ⊓ Subgroup.normalizer (intersection : Set GroupType)
  let secondNormalizer := second ⊓ Subgroup.normalizer (intersection : Set GroupType)
  have intersection_normalized := normalizer_inf_of_le actor first second
    first_normalized second_normalized
  have normalizer_normalized := normalizer_normalized actor intersection intersection_normalized
  have firstNormalizer_normalized := normalizer_inf_of_le actor first
    (Subgroup.normalizer (intersection : Set GroupType)) first_normalized normalizer_normalized
  have secondNormalizer_normalized := normalizer_inf_of_le actor second
    (Subgroup.normalizer (intersection : Set GroupType)) second_normalized normalizer_normalized
  have first_invariant : ∀ actorElement : actor, ∀ element ∈ firstNormalizer,
      actorElement • element ∈ firstNormalizer := by
    intro actorElement element member
    exact Subgroup.le_normalizer_iff.mp firstNormalizer_normalized actorElement.val
      actorElement.property element member
  have second_invariant : ∀ actorElement : actor, ∀ element ∈ secondNormalizer,
      actorElement • element ∈ secondNormalizer := by
    intro actorElement element member
    exact Subgroup.le_normalizer_iff.mp secondNormalizer_normalized actorElement.val
      actorElement.property element member
  have exponent : ∀ element : actor, element ^ prime = 1 := by
    intro element
    apply Subtype.ext
    exact elementary.2 element.val element.property
  have first_coprime : Nat.Coprime prime (Nat.card firstNormalizer) :=
    prime_coprime_pgroup_card prime groupPrime prime_prime groupPrime_prime distinct
      (first_pgroup.to_le inf_le_left)
  have second_coprime : Nat.Coprime prime (Nat.card secondNormalizer) :=
    prime_coprime_pgroup_card prime groupPrime prime_prime groupPrime_prime distinct
      (second_pgroup.to_le inf_le_left)
  obtain ⟨internal, internal_card, first_escape, second_escape⟩ :=
    invariant_subgroups_pair_fixed_growth actor prime rank prime_prime exponent large
      firstNormalizer secondNormalizer intersection first_invariant second_invariant
      first_coprime second_coprime
      (pgroup_normalizer_strict_growth groupPrime groupPrime_prime first intersection
        first_pgroup first_proper).not_ge
      (pgroup_normalizer_strict_growth groupPrime groupPrime_prime second intersection
        second_pgroup second_proper).not_ge
  let embedded := internal.map actor.subtype
  have embedded_le : embedded ≤ actor := by
    rintro element ⟨representative, _, rfl⟩
    exact representative.property
  have embedded_card : Nat.card embedded = prime ^ rank := by
    rw [Subgroup.card_map_of_injective actor.subtype_injective]
    exact internal_card
  rw [ambient_subgroup_fixed_eq_centralizer actor internal] at first_escape second_escape
  exact ⟨embedded, ⟨embedded_le, embedded_card⟩, first_escape, second_escape⟩

end CFSG.SignalizerFunctor.Helpers
