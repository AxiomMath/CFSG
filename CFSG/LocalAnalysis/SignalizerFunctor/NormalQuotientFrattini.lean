module

public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductIndices
public import CFSG.LocalAnalysis.SignalizerFunctor.ActionPrimeCore

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem normal_subgroup_sylow_intersection (prime : ℕ) (prime_prime : prime.Prime)
    (normal : Subgroup GroupType) [normal.Normal] (sylow : Sylow prime GroupType) :
    ∃ result : Sylow prime normal,
      (result : Subgroup normal).map normal.subtype = normal ⊓ (sylow : Subgroup GroupType) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have index_divides : (sylow : Subgroup GroupType).relIndex normal ∣
      (sylow : Subgroup GroupType).index := by
    simpa only [Subgroup.relIndex_top_right] using
      normalizing_subgroup_relIndex_dvd (⊤ : Subgroup GroupType) normal
        (sylow : Subgroup GroupType) le_top le_top Subgroup.le_normalizer_of_normal
  have not_divides : ¬ prime ∣ ((sylow : Subgroup GroupType).subgroupOf normal).index := by
    intro divides
    exact sylow.not_dvd_index (divides.trans index_divides)
  have pgroup : IsPGroup prime ((sylow : Subgroup GroupType).subgroupOf normal) :=
    sylow.isPGroup'.comap_of_injective normal.subtype normal.subtype_injective
  refine ⟨pgroup.toSylow not_divides, ?_⟩
  rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem normal_pgroup_quotient_sylow_product (prime : ℕ) (prime_prime : prime.Prime)
    (kernel parent : Subgroup GroupType) [kernel.Normal] (kernel_le : kernel ≤ parent)
    (image_pgroup : IsPGroup prime (parent.map (QuotientGroup.mk' kernel)))
    (sylow : Sylow prime parent) :
    parent = kernel ⊔ (sylow : Subgroup parent).map parent.subtype := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let projection := QuotientGroup.mk' kernel
  let restricted := subgroupImageHom projection parent
  let imageSylow := sylow.mapSurjective (subgroup_image_hom_surjective projection parent)
  have image_full : (imageSylow : Subgroup (parent.map projection)) = ⊤ := by
    exact (imageSylow.is_maximal' (image_pgroup.to_subgroup ⊤) le_top).symm
  have mapped_full := congrArg (Subgroup.map (parent.map projection).subtype) image_full
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, ← MonoidHom.range_eq_map,
    Subgroup.subtype_range] at mapped_full
  have hom_eq : (parent.map projection).subtype.comp restricted = projection.comp parent.subtype := by
    ext element
    rfl
  change (sylow : Subgroup parent).map ((parent.map projection).subtype.comp restricted) =
    parent.map projection at mapped_full
  rw [hom_eq, ← Subgroup.map_map] at mapped_full
  have preimage_eq := congrArg (Subgroup.comap projection) mapped_full
  rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq_self (by
    simpa only [projection, QuotientGroup.ker_mk'] using kernel_le)] at preimage_eq
  simpa only [projection, QuotientGroup.ker_mk', sup_comm] using preimage_eq.symm

theorem normal_pgroup_quotient_frattini (prime : ℕ) (prime_prime : prime.Prime)
    (kernel parent : Subgroup GroupType) [kernel.Normal] [parent.Normal]
    (kernel_le : kernel ≤ parent)
    (image_pgroup : IsPGroup prime (parent.map (QuotientGroup.mk' kernel)))
    (sylow : Sylow prime parent) :
    kernel ⊔ Subgroup.normalizer
      ((sylow : Subgroup parent).map parent.subtype : Set GroupType) = ⊤ := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have product := normal_pgroup_quotient_sylow_product prime prime_prime kernel parent
    kernel_le image_pgroup sylow
  have frattini := sylow.normalizer_sup_eq_top
  conv at frattini => lhs; rhs; rw [product]
  rw [sup_comm, sup_assoc] at frattini
  have contained : (sylow : Subgroup parent).map parent.subtype ≤
      Subgroup.normalizer ((sylow : Subgroup parent).map parent.subtype : Set GroupType) :=
    Subgroup.le_normalizer
  rwa [sup_eq_right.mpr contained] at frattini

theorem quotient_action_prime_core_frattini (prime : ℕ) (prime_prime : prime.Prime)
    (kernel : Subgroup GroupType) [kernel.Normal]
    (sylow : Sylow prime (quotientActionPrimeCore prime kernel)) :
    quotientActionPrimeCore prime kernel = kernel ⊔
      (sylow : Subgroup (quotientActionPrimeCore prime kernel)).map
        (quotientActionPrimeCore prime kernel).subtype ∧
    kernel ⊔ Subgroup.normalizer
      ((sylow : Subgroup (quotientActionPrimeCore prime kernel)).map
        (quotientActionPrimeCore prime kernel).subtype : Set GroupType) = ⊤ := by
  let := quotient_action_prime_core_normal prime kernel
  have contained := kernel_le_quotient_action_prime_core prime kernel
  have pgroup := quotient_action_prime_core_image_pgroup prime prime_prime kernel
  exact ⟨normal_pgroup_quotient_sylow_product prime prime_prime kernel _ contained pgroup sylow,
    normal_pgroup_quotient_frattini prime prime_prime kernel _ contained pgroup sylow⟩

end CFSG.SignalizerFunctor.Helpers
