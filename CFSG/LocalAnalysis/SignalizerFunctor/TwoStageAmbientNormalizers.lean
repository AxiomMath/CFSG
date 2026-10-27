module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedGrowth
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageSylowNormalizers

public section

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem subgroup_center_map_injective {ImageType : Type imageUniverse} [Group ImageType]
    (homomorphism : GroupType →* ImageType) (injective : Function.Injective homomorphism)
    (subgroup : Subgroup GroupType) :
    ((Subgroup.center subgroup).map subgroup.subtype).map homomorphism =
      (Subgroup.center (subgroup.map homomorphism)).map (subgroup.map homomorphism).subtype := by
  let equivalence := subgroup.equivMapOfInjective homomorphism injective
  have center_eq : (Subgroup.center subgroup).map equivalence.toMonoidHom =
      Subgroup.center (subgroup.map homomorphism) := by
    ext element
    constructor
    · rintro ⟨representative, member, rfl⟩
      exact ((Subgroup.centerCongr equivalence) ⟨representative, member⟩).property
    · intro member
      let original := (Subgroup.centerCongr equivalence).symm ⟨element, member⟩
      refine ⟨original.val, original.property, ?_⟩
      exact congrArg Subtype.val
        ((Subgroup.centerCongr equivalence).apply_symm_apply ⟨element, member⟩)
  have mapped_eq := congrArg (Subgroup.map (subgroup.map homomorphism).subtype) center_eq
  rw [Subgroup.map_map] at mapped_eq
  rw [Subgroup.map_map]
  have hom_eq : (subgroup.map homomorphism).subtype.comp equivalence.toMonoidHom =
      homomorphism.comp subgroup.subtype := by
    ext element
    rfl
  rw [hom_eq] at mapped_eq
  exact mapped_eq

theorem normalizer_subtype_map (parent : Subgroup GroupType) (subgroup : Subgroup parent) :
    (Subgroup.normalizer (subgroup : Set parent)).map parent.subtype =
      parent ⊓ Subgroup.normalizer (subgroup.map parent.subtype : Set GroupType) := by
  have equal := normalizer_subgroupOf_map parent (subgroup.map parent.subtype)
    (Subgroup.map_subtype_le _)
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective parent.subtype_injective] at equal
  exact equal

variable [Finite GroupType]

theorem two_stage_ambient_sylow_lift (prime : ℕ) (prime_prime : prime.Prime)
    (parent : Subgroup GroupType)
    (sylow : Sylow prime ((twoStageCore (GroupType := parent) prime).map parent.subtype)) :
    ∃ internalSylow : Sylow prime (twoStageCore (GroupType := parent) prime),
      ((internalSylow : Subgroup (twoStageCore (GroupType := parent) prime)).map
        (twoStageCore prime).subtype).map parent.subtype =
          (sylow : Subgroup ((twoStageCore (GroupType := parent) prime).map parent.subtype)).map
            ((twoStageCore (GroupType := parent) prime).map parent.subtype).subtype := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let core := twoStageCore (GroupType := parent) prime
  let equivalence := core.equivMapOfInjective parent.subtype parent.subtype_injective
  have internalSurjective : Function.Surjective equivalence.symm.toMonoidHom :=
    equivalence.symm.surjective
  let internalSylow := sylow.mapSurjective (f := equivalence.symm.toMonoidHom)
    internalSurjective
  refine ⟨internalSylow, ?_⟩
  change ((sylow.mapSurjective (f := equivalence.symm.toMonoidHom)
    internalSurjective : Subgroup core).map core.subtype).map parent.subtype = _
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext element
  have inverse_eq := congrArg (fun value : core.map parent.subtype => value.val)
    (equivalence.apply_symm_apply element)
  exact inverse_eq

theorem two_stage_ambient_sylow_normalizer_factorization
    (prime : ℕ) (prime_prime : prime.Prime) (parent : Subgroup GroupType)
    (sylow : Sylow prime ((twoStageCore (GroupType := parent) prime).map parent.subtype)) :
    parent = (primeSetCore (GroupType := parent) ({prime}ᶜ)).map parent.subtype ⊔
      (parent ⊓ Subgroup.normalizer
        (((sylow : Subgroup ((twoStageCore (GroupType := parent) prime).map parent.subtype)).map
          ((twoStageCore (GroupType := parent) prime).map parent.subtype).subtype) : Set GroupType)) := by
  obtain ⟨internalSylow, mapped_eq⟩ := two_stage_ambient_sylow_lift prime prime_prime parent sylow
  have internal_factorization := two_stage_sylow_normalizer_factorization prime prime_prime internalSylow
  have mapped_factorization := congrArg (Subgroup.map parent.subtype) internal_factorization
  rw [Subgroup.map_sup, normalizer_subtype_map, ← MonoidHom.range_eq_map,
    parent.subtype_range, mapped_eq] at mapped_factorization
  exact mapped_factorization.symm

theorem two_stage_ambient_sylow_center_normalizer_factorization
    (prime : ℕ) (prime_prime : prime.Prime) (parent : Subgroup GroupType)
    (sylow : Sylow prime ((twoStageCore (GroupType := parent) prime).map parent.subtype)) :
    let embedded := (sylow : Subgroup ((twoStageCore (GroupType := parent) prime).map parent.subtype)).map
      ((twoStageCore (GroupType := parent) prime).map parent.subtype).subtype
    parent = (primeSetCore (GroupType := parent) ({prime}ᶜ)).map parent.subtype ⊔
      (parent ⊓ Subgroup.normalizer
        ((Subgroup.center embedded).map embedded.subtype : Set GroupType)) := by
  obtain ⟨internalSylow, mapped_eq⟩ := two_stage_ambient_sylow_lift prime prime_prime parent sylow
  have internal_factorization :=
    two_stage_sylow_center_normalizer_factorization prime prime_prime internalSylow
  have mapped_factorization := congrArg (Subgroup.map parent.subtype) internal_factorization
  rw [Subgroup.map_sup, normalizer_subtype_map, ← MonoidHom.range_eq_map,
    parent.subtype_range, subgroup_center_map_injective parent.subtype parent.subtype_injective,
    mapped_eq] at mapped_factorization
  exact mapped_factorization.symm

end CFSG.SignalizerFunctor.Helpers
