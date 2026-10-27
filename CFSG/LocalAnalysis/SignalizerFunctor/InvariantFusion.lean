module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowConjugacy
public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleProduct
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowContainment
public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleConjugation

public section

universe actorUniverse groupUniverse targetUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

theorem conjugate_subgroup_map
    {GroupType : Type groupUniverse} [Group GroupType]
    {TargetType : Type targetUniverse} [Group TargetType]
    (hom : GroupType →* TargetType) (element : GroupType) (subgroup : Subgroup GroupType) :
    (conjugateSubgroup element subgroup).map hom =
      conjugateSubgroup (hom element) (subgroup.map hom) := by
  change (subgroup.map (MulAut.conj element).toMonoidHom).map hom =
    (subgroup.map hom).map (MulAut.conj (hom element)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext value
  change hom (element * value * element⁻¹) = hom element * hom value * (hom element)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem invariant_prime_subgroups_fuse
    (prime groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime)
    (ActorType : Type actorUniverse) [Group ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (first second : Subgroup GroupType)
    (first_pgroup : IsPGroup groupPrime first)
    (second_pgroup : IsPGroup groupPrime second)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first,
      actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second,
      actorElement • element ∈ second) :
    ∃ element : GroupType, (∀ actorElement : ActorType, actorElement • element = element) ∧
      ∃ combined : Subgroup GroupType, IsPGroup groupPrime combined ∧
        (∀ actorElement : ActorType, ∀ value ∈ combined, actorElement • value ∈ combined) ∧
        conjugateSubgroup element first ≤ combined ∧ second ≤ combined := by
  obtain ⟨firstSylow, first_contains, first_fixed⟩ := invariant_sylow_containing prime
    groupPrime prime_prime groupPrime_prime actor_pgroup coprime first first_pgroup first_invariant
  obtain ⟨secondSylow, second_contains, second_fixed⟩ := invariant_sylow_containing prime
    groupPrime prime_prime groupPrime_prime actor_pgroup coprime second second_pgroup second_invariant
  obtain ⟨element, conjugates, fixed⟩ := invariant_sylows_conjugate_by_fixed_element prime
    groupPrime prime_prime groupPrime_prime ActorType actor_pgroup GroupType coprime
    firstSylow secondSylow first_fixed second_fixed
  refine ⟨element, fixed, secondSylow, secondSylow.isPGroup', ?_, ?_, second_contains⟩
  · intro actorElement value member
    have image_fixed : actorElement • (secondSylow : Subgroup GroupType) = secondSylow := by
      rw [← Sylow.pointwise_smul_def, second_fixed]
    rw [← image_fixed]
    exact Subgroup.smul_mem_pointwise_smul value actorElement _ member
  · have conjugated_contains := Subgroup.map_mono
      (f := (MulAut.conj element).toMonoidHom) first_contains
    have equality : conjugateSubgroup element (firstSylow : Subgroup GroupType) = secondSylow :=
      congrArg (fun sylow : Sylow groupPrime GroupType => (sylow : Subgroup GroupType)) conjugates
    change conjugateSubgroup element first ≤
      conjugateSubgroup element (firstSylow : Subgroup GroupType) at conjugated_contains
    rwa [equality] at conjugated_contains

theorem normalizer_normalized
    {GroupType : Type groupUniverse} [Group GroupType]
    (actor target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    actor ≤ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType) := by
  let _action := ambientConjugationAction actor
  let _baseAction : MulAction actor GroupType := _action.toMulAction
  have invariant : ∀ actorElement : actor, ∀ element ∈ target,
      actorElement • element ∈ target := by
    intro actorElement element member
    exact Subgroup.le_normalizer_iff.mp normalized actorElement.val actorElement.property
      element member
  have normalizer_invariant := normalizer_invariant_of_invariant target invariant
  apply Subgroup.le_normalizer_iff.mpr
  intro actorElement actor_member element member
  exact normalizer_invariant ⟨actorElement, actor_member⟩ element member

theorem normalized_prime_subgroups_fuse
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (prime groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime) (actor target first second : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor)
    (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (target_coprime : Nat.Coprime prime (Nat.card target))
    (first_le : first ≤ target) (second_le : second ≤ target)
    (first_pgroup : IsPGroup groupPrime first) (second_pgroup : IsPGroup groupPrime second)
    (first_normalized : actor ≤ Subgroup.normalizer (first : Set GroupType))
    (second_normalized : actor ≤ Subgroup.normalizer (second : Set GroupType)) :
    ∃ element ∈ target ⊓ Subgroup.centralizer (actor : Set GroupType),
      ∃ combined : Subgroup GroupType, IsPGroup groupPrime combined ∧
        actor ≤ Subgroup.normalizer (combined : Set GroupType) ∧ combined ≤ target ∧
        conjugateSubgroup element first ≤ combined ∧ second ≤ combined := by
  let _action := conjugationAction actor target target_normalized
  have first_internal_invariant : ∀ actorElement : actor,
      ∀ element ∈ first.subgroupOf target, actorElement • element ∈ first.subgroupOf target := by
    intro actorElement element member
    exact Subgroup.le_normalizer_iff.mp first_normalized actorElement.val actorElement.property
      element.val member
  have second_internal_invariant : ∀ actorElement : actor,
      ∀ element ∈ second.subgroupOf target, actorElement • element ∈ second.subgroupOf target := by
    intro actorElement element member
    exact Subgroup.le_normalizer_iff.mp second_normalized actorElement.val actorElement.property
      element.val member
  obtain ⟨element, fixed, internalCombined, combined_pgroup, combined_invariant,
    first_contains, second_contains⟩ := invariant_prime_subgroups_fuse prime groupPrime
      prime_prime groupPrime_prime actor actor_pgroup target target_coprime
      (first.subgroupOf target) (second.subgroupOf target)
      (first_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe first_le).symm)
      (second_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe second_le).symm)
      first_internal_invariant second_internal_invariant
  let combined := internalCombined.map target.subtype
  refine ⟨element.val, ⟨element.property, ?_⟩, combined,
    combined_pgroup.map target.subtype, ?_, ?_, ?_, ?_⟩
  · apply Subgroup.mem_centralizer_iff.mpr
    intro actorElement member
    have equality := congrArg (fun internal : target => (internal : GroupType))
      (fixed (⟨actorElement, member⟩ : actor))
    exact mul_inv_eq_iff_eq_mul.mp equality
  · apply Subgroup.le_normalizer_iff.mpr
    intro actorElement actor_member value member
    obtain ⟨representative, representative_member, rfl⟩ := member
    refine ⟨(⟨actorElement, actor_member⟩ : actor) • representative,
      combined_invariant ⟨actorElement, actor_member⟩ representative representative_member, rfl⟩
  · rintro value ⟨representative, _, rfl⟩
    exact representative.property
  · have mapped_contains := Subgroup.map_mono (f := target.subtype) first_contains
    rwa [conjugate_subgroup_map, Subgroup.map_subgroupOf_eq_of_le first_le] at mapped_contains
  · have mapped_contains := Subgroup.map_mono (f := target.subtype) second_contains
    rwa [Subgroup.map_subgroupOf_eq_of_le second_le] at mapped_contains

end CFSG.SignalizerFunctor.Helpers
