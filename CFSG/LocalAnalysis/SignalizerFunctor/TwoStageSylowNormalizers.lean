module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeValueHull
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem normalizer_le_normalizer_characteristic (parent : Subgroup GroupType)
    (internal : Subgroup parent) [internal.Characteristic] :
    Subgroup.normalizer (parent : Set GroupType) ≤
      Subgroup.normalizer (internal.map parent.subtype : Set GroupType) := by
  let actor := Subgroup.normalizer (parent : Set GroupType)
  let _action := conjugationAction actor parent le_rfl
  apply invariant_subgroup_map_normalized actor parent le_rfl internal
  change ∀ actorElement : actor, ∀ element ∈ internal, actorElement • element ∈ internal
  intro actorElement element member
  exact Subgroup.characteristic_iff_le_comap.mp inferInstance
    (MulDistribMulAction.toMulEquiv parent actorElement) member

theorem two_stage_sylow_image (prime : ℕ) (prime_prime : prime.Prime)
    (sylow : Sylow prime (twoStageCore (GroupType := GroupType) prime)) :
    let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
    let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
    ((sylow : Subgroup (twoStageCore (GroupType := GroupType) prime)).map
      (twoStageCore prime).subtype).map (QuotientGroup.mk' complement) =
        primeSetCore (GroupType := GroupType ⧸ complement) {prime} := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  let core := twoStageCore (GroupType := GroupType) prime
  let quotientCore := primeSetCore (GroupType := GroupType ⧸ complement) {prime}
  let projection := QuotientGroup.mk' complement
  let restricted : core →* quotientCore := (projection.domRestrict core).codRestrict quotientCore
    (fun element => element.property)
  have restricted_surjective : Function.Surjective restricted := by
    intro element
    obtain ⟨representative, equality⟩ := QuotientGroup.mk'_surjective complement element.val
    have member : representative ∈ core := by
      change projection representative ∈ quotientCore
      rw [equality]
      exact element.property
    exact ⟨⟨representative, member⟩, Subtype.ext equality⟩
  let imageSylow := sylow.mapSurjective restricted_surjective
  have image_top : (imageSylow : Subgroup quotientCore) = ⊤ :=
    (imageSylow.is_maximal'
      ((prime_core_isPGroup (GroupType := GroupType ⧸ complement) prime prime_prime).to_subgroup ⊤)
      le_top).symm
  have mapped_equal := congrArg (Subgroup.map quotientCore.subtype) image_top
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, ← MonoidHom.range_eq_map,
    quotientCore.subtype_range] at mapped_equal
  change ((sylow : Subgroup core).map core.subtype).map projection = quotientCore
  rw [Subgroup.map_map]
  have composition : quotientCore.subtype.comp restricted = projection.comp core.subtype := by
    ext element
    rfl
  rwa [composition] at mapped_equal

theorem two_stage_sylow_product (prime : ℕ) (prime_prime : prime.Prime)
    (sylow : Sylow prime (twoStageCore (GroupType := GroupType) prime)) :
    primeSetCore (GroupType := GroupType) ({prime}ᶜ) ⊔
      (sylow : Subgroup (twoStageCore (GroupType := GroupType) prime)).map
        (twoStageCore prime).subtype = twoStageCore (GroupType := GroupType) prime := by
  let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  have mapped_equal := two_stage_sylow_image prime prime_prime sylow
  have preimage_equal := congrArg (Subgroup.comap (QuotientGroup.mk' complement)) mapped_equal
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at preimage_equal
  exact (sup_comm _ _).trans preimage_equal

theorem two_stage_sylow_normalizer_factorization (prime : ℕ) (prime_prime : prime.Prime)
    (sylow : Sylow prime (twoStageCore (GroupType := GroupType) prime)) :
    primeSetCore (GroupType := GroupType) ({prime}ᶜ) ⊔ Subgroup.normalizer
      (((sylow : Subgroup (twoStageCore (GroupType := GroupType) prime)).map
        (twoStageCore prime).subtype : Subgroup GroupType) : Set GroupType) = ⊤ := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let _normal := two_stage_core_normal (GroupType := GroupType) prime
  let embedded := (sylow : Subgroup (twoStageCore (GroupType := GroupType) prime)).map
    (twoStageCore prime).subtype
  have frattini := sylow.normalizer_sup_eq_top
  have core_product := two_stage_sylow_product prime prime_prime sylow
  apply top_le_iff.mp
  rw [← frattini]
  apply sup_le
  · exact le_sup_right
  · conv_lhs => rw [← core_product]
    exact sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right)

theorem two_stage_sylow_center_normalizer_factorization (prime : ℕ) (prime_prime : prime.Prime)
    (sylow : Sylow prime (twoStageCore (GroupType := GroupType) prime)) :
    let embedded := (sylow : Subgroup (twoStageCore (GroupType := GroupType) prime)).map
      (twoStageCore prime).subtype
    primeSetCore (GroupType := GroupType) ({prime}ᶜ) ⊔ Subgroup.normalizer
      ((Subgroup.center embedded).map embedded.subtype : Set GroupType) = ⊤ := by
  let embedded := (sylow : Subgroup (twoStageCore (GroupType := GroupType) prime)).map
    (twoStageCore prime).subtype
  apply top_le_iff.mp
  rw [← two_stage_sylow_normalizer_factorization prime prime_prime sylow]
  exact sup_le le_sup_left
    ((normalizer_le_normalizer_characteristic embedded (Subgroup.center embedded)).trans le_sup_right)

end CFSG.SignalizerFunctor.Helpers
