module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedNormalizedPrimeHull
public import CFSG.LocalAnalysis.SignalizerFunctor.CentralizerImages

public section

universe actorUniverse groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]
variable [MulDistribMulAction ActorType GroupType] [MulDistribMulAction ActorType ImageType]

theorem fixed_normalized_prime_hull_map_le (primes : Set ℕ) (equivalence : GroupType ≃* ImageType)
    (equivariant : ∀ actorElement : ActorType, ∀ element : GroupType,
      equivalence (actorElement • element) = actorElement • equivalence element) :
    (fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := GroupType) primes).map
      equivalence.toMonoidHom ≤
        fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := ImageType) primes := by
  rw [fixedNormalizedPrimeHull, Subgroup.map_iSup]
  apply iSup_le
  intro candidate
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro property
  apply fixed_normalized_prime_hull_contains
  · rw [Subgroup.card_map_of_injective equivalence.injective]
    exact property.1
  · intro actorElement imageElement member
    obtain ⟨element, element_member, rfl⟩ := member
    exact ⟨actorElement • element, property.2.1 actorElement element element_member,
      equivariant actorElement element⟩
  · intro imageElement fixed
    have original_fixed : equivalence.symm imageElement ∈ FixedPoints.subgroup ActorType GroupType := by
      intro actorElement
      apply equivalence.injective
      rw [equivariant, equivalence.apply_symm_apply, fixed actorElement]
    have mapped_normalizer := normalizer_image_le equivalence.toMonoidHom
      (FixedPoints.subgroup ActorType GroupType) candidate property.2.2
    apply mapped_normalizer
    exact ⟨equivalence.symm imageElement, original_fixed, equivalence.apply_symm_apply imageElement⟩

theorem fixed_normalized_prime_hull_map_equiv (primes : Set ℕ)
    (equivalence : GroupType ≃* ImageType)
    (equivariant : ∀ actorElement : ActorType, ∀ element : GroupType,
      equivalence (actorElement • element) = actorElement • equivalence element) :
    (fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := GroupType) primes).map
      equivalence.toMonoidHom =
        fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := ImageType) primes := by
  apply le_antisymm (fixed_normalized_prime_hull_map_le primes equivalence equivariant)
  have inverse_equivariant : ∀ actorElement : ActorType, ∀ imageElement : ImageType,
      equivalence.symm (actorElement • imageElement) = actorElement • equivalence.symm imageElement := by
    intro actorElement imageElement
    apply equivalence.injective
    rw [equivalence.apply_symm_apply, equivariant, equivalence.apply_symm_apply]
  have inverse_le := fixed_normalized_prime_hull_map_le primes equivalence.symm inverse_equivariant
  have mapped_le := Subgroup.map_mono (f := equivalence.toMonoidHom) inverse_le
  rw [Subgroup.map_map] at mapped_le
  have composition : equivalence.toMonoidHom.comp equivalence.symm.toMonoidHom =
      MonoidHom.id ImageType := by
    ext element
    exact equivalence.apply_symm_apply element
  rwa [composition, Subgroup.map_id] at mapped_le

end CFSG.SignalizerFunctor.Helpers
