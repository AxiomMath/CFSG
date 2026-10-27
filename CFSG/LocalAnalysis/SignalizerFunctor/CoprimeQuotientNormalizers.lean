module

public import CFSG.LocalAnalysis.SignalizerFunctor.LocalSylowIntersections
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalPrimeSupplements

public section

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem pgroup_sylow_in_normal_sup (prime : ℕ) (prime_prime : prime.Prime)
    (normal subgroup : Subgroup GroupType) [normal.Normal]
    (normal_coprime : Nat.Coprime prime (Nat.card normal)) (pgroup : IsPGroup prime subgroup) :
    ∃ sylow : Sylow prime ↥(normal ⊔ subgroup),
      (sylow : Subgroup ↥(normal ⊔ subgroup)) = subgroup.subgroupOf (normal ⊔ subgroup) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let combined := normal ⊔ subgroup
  let internalNormal := normal.subgroupOf combined
  let internalSubgroup := subgroup.subgroupOf combined
  let _normal : internalNormal.Normal := Subgroup.Normal.subgroupOf inferInstance combined
  have internal_whole : internalNormal ⊔ internalSubgroup = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have internal_coprime : Nat.Coprime prime (Nat.card internalNormal) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : normal ≤ combined)).toEquiv]
    exact normal_coprime
  have index_coprime := internal_coprime.of_dvd_right
    (supplement_index_dvd_normal_card internalNormal internalSubgroup internal_whole)
  have internal_pgroup : IsPGroup prime internalSubgroup := pgroup.of_equiv
    (Subgroup.subgroupOfEquivOfLe (le_sup_right : subgroup ≤ combined)).symm
  exact ⟨internal_pgroup.toSylow (prime_prime.coprime_iff_not_dvd.mp index_coprime),
    IsPGroup.toSylow_coe _ _⟩

theorem coprime_quotient_normalizer_image (prime : ℕ) (prime_prime : prime.Prime)
    (normal subgroup : Subgroup GroupType) [normal.Normal]
    (normal_coprime : Nat.Coprime prime (Nat.card normal)) (pgroup : IsPGroup prime subgroup) :
    (Subgroup.normalizer (subgroup : Set GroupType)).map (QuotientGroup.mk' normal) =
      Subgroup.normalizer (subgroup.map (QuotientGroup.mk' normal) : Set (GroupType ⧸ normal)) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let projection := QuotientGroup.mk' normal
  apply le_antisymm (Subgroup.le_normalizer_map projection)
  intro imageElement normalized
  obtain ⟨element, image_eq⟩ := QuotientGroup.mk'_surjective normal imageElement
  let combined := normal ⊔ subgroup
  have conjugate_contained : conjugateSubgroup element subgroup ≤ combined := by
    rintro representative ⟨original, member, rfl⟩
    have image_member : projection (element * original * element⁻¹) ∈ subgroup.map projection := by
      rw [map_mul, map_mul, map_inv, image_eq]
      exact Subgroup.le_normalizer_iff.mp le_rfl imageElement normalized (projection original)
        (Subgroup.mem_map_of_mem projection member)
    have preimage_member : element * original * element⁻¹ ∈ (subgroup.map projection).comap projection :=
      image_member
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm] at preimage_member
    exact preimage_member
  obtain ⟨firstSylow, first_eq⟩ := pgroup_sylow_in_normal_sup prime prime_prime normal subgroup
    normal_coprime pgroup
  have conjugate_pgroup : IsPGroup prime ((conjugateSubgroup element subgroup).subgroupOf combined) :=
    (pgroup.map (MulAut.conj element).toMonoidHom).of_equiv
      (Subgroup.subgroupOfEquivOfLe conjugate_contained).symm
  have conjugate_card : Nat.card ((conjugateSubgroup element subgroup).subgroupOf combined) =
      Nat.card (firstSylow : Subgroup combined) := by
    rw [first_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe conjugate_contained).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : subgroup ≤ combined)).toEquiv,
      conjugate_subgroup_card]
  obtain ⟨secondSylow, second_eq⟩ := pgroup_sylow_of_card_eq prime prime_prime _ conjugate_pgroup
    firstSylow conjugate_card
  obtain ⟨conjugator, sylow_eq⟩ := MulAction.exists_smul_eq combined secondSylow firstSylow
  have subgroup_eq := congrArg (fun sylow : Sylow prime combined => (sylow : Subgroup combined)) sylow_eq
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, second_eq, first_eq] at subgroup_eq
  change conjugateSubgroup conjugator
    ((conjugateSubgroup element subgroup).subgroupOf combined) = subgroup.subgroupOf combined
    at subgroup_eq
  have mapped_eq := congrArg (Subgroup.map combined.subtype) subgroup_eq
  rw [conjugate_subgroup_map,
    Subgroup.map_subgroupOf_eq_of_le conjugate_contained,
    Subgroup.map_subgroupOf_eq_of_le (le_sup_right : subgroup ≤ combined),
    conjugate_subgroup_mul] at mapped_eq
  have product_normalized : conjugator.val * element ∈ Subgroup.normalizer (subgroup : Set GroupType) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr mapped_eq
  obtain ⟨normalElement, normal_member, subgroupElement, subgroup_member, product_eq⟩ :=
    Subgroup.mem_sup_of_normal_left.mp conjugator.property
  let representative := subgroupElement⁻¹ * (conjugator.val * element)
  have representative_normalized : representative ∈ Subgroup.normalizer (subgroup : Set GroupType) :=
    (Subgroup.normalizer (subgroup : Set GroupType)).mul_mem
      (Subgroup.le_normalizer (subgroup.inv_mem subgroup_member)) product_normalized
  refine ⟨representative, representative_normalized, ?_⟩
  have normal_trivial : projection normalElement = 1 := (QuotientGroup.eq_one_iff _).mpr normal_member
  change projection (subgroupElement⁻¹ * (conjugator.val * element)) = imageElement
  rw [← product_eq, map_mul, map_inv, map_mul, map_mul, normal_trivial, one_mul,
    ← mul_assoc, inv_mul_cancel, one_mul, image_eq]

theorem coprime_surjective_normalizer_image
    {ImageType : Type imageUniverse} [Group ImageType]
    (prime : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (surjective : Function.Surjective homomorphism)
    (subgroup : Subgroup GroupType)
    (kernel_coprime : Nat.Coprime prime (Nat.card homomorphism.ker))
    (pgroup : IsPGroup prime subgroup) :
    (Subgroup.normalizer (subgroup : Set GroupType)).map homomorphism =
      Subgroup.normalizer (subgroup.map homomorphism : Set ImageType) := by
  let equivalence := QuotientGroup.quotientKerEquivOfSurjective homomorphism surjective
  have hom_eq : equivalence.toMonoidHom.comp (QuotientGroup.mk' homomorphism.ker) =
      homomorphism := by
    ext element
    rfl
  have normalizer_eq := congrArg (Subgroup.map equivalence.toMonoidHom)
    (coprime_quotient_normalizer_image prime prime_prime homomorphism.ker subgroup
      kernel_coprime pgroup)
  rw [Subgroup.map_map, hom_eq, Subgroup.map_equiv_normalizer_eq,
    Subgroup.map_map, hom_eq] at normalizer_eq
  exact normalizer_eq

theorem normalizer_product_coprime_kernel (prime : ℕ) (prime_prime : prime.Prime)
    (normal supplement subgroup : Subgroup GroupType) [normal.Normal]
    (normal_coprime : Nat.Coprime prime (Nat.card normal))
    (whole : normal ⊔ supplement = ⊤) (contained : subgroup ≤ supplement)
    (pgroup : IsPGroup prime subgroup) :
    ∀ element ∈ Subgroup.normalizer (subgroup : Set GroupType),
      ∃ normalElement ∈ normal ⊓ Subgroup.normalizer (subgroup : Set GroupType),
        ∃ supplementElement ∈ supplement ⊓ Subgroup.normalizer (subgroup : Set GroupType),
          normalElement * supplementElement = element := by
  let projection := QuotientGroup.mk' normal
  let homomorphism := projection.comp supplement.subtype
  have surjective : Function.Surjective homomorphism := by
    intro imageElement
    obtain ⟨element, image_eq⟩ := QuotientGroup.mk'_surjective normal imageElement
    have member : element ∈ normal ⊔ supplement := by rw [whole]; trivial
    obtain ⟨normalElement, normal_member, supplementElement, supplement_member, product_eq⟩ :=
      Subgroup.mem_sup_of_normal_left.mp member
    refine ⟨⟨supplementElement, supplement_member⟩, ?_⟩
    change projection supplementElement = imageElement
    have normal_trivial : projection normalElement = 1 :=
      (QuotientGroup.eq_one_iff _).mpr normal_member
    rw [← product_eq, map_mul, normal_trivial, one_mul] at image_eq
    exact image_eq
  have kernel_eq : homomorphism.ker = normal.subgroupOf supplement := by
    ext element
    change projection element.val = 1 ↔ element.val ∈ normal
    exact QuotientGroup.eq_one_iff _
  have kernel_coprime : Nat.Coprime prime (Nat.card homomorphism.ker) := by
    rw [kernel_eq]
    exact normal_coprime.of_dvd_right
      (Subgroup.card_comap_dvd_of_injective normal supplement.subtype supplement.subtype_injective)
  have internal_pgroup : IsPGroup prime (subgroup.subgroupOf supplement) :=
    pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe contained).symm
  have image_subgroup : (subgroup.subgroupOf supplement).map homomorphism =
      subgroup.map projection := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le contained]
  have normalizer_eq := coprime_surjective_normalizer_image prime prime_prime homomorphism
    surjective (subgroup.subgroupOf supplement) kernel_coprime internal_pgroup
  rw [image_subgroup] at normalizer_eq
  intro element normalized
  have image_normalized : projection element ∈
      Subgroup.normalizer (subgroup.map projection : Set (GroupType ⧸ normal)) :=
    Subgroup.le_normalizer_map projection (Subgroup.mem_map_of_mem projection normalized)
  rw [← normalizer_eq] at image_normalized
  obtain ⟨representative, representative_normalized, image_eq⟩ := image_normalized
  have supplement_normalized : representative.val ∈
      Subgroup.normalizer (subgroup : Set GroupType) := by
    have member := Subgroup.mem_map_of_mem supplement.subtype representative_normalized
    rw [normalizer_subgroupOf_map supplement subgroup contained] at member
    exact member.2
  let normalElement := element * representative.val⁻¹
  have normal_member : normalElement ∈ normal := by
    apply (QuotientGroup.eq_one_iff _).mp
    change projection (element * representative.val⁻¹) = 1
    change projection representative.val = projection element at image_eq
    rw [map_mul, map_inv, image_eq, mul_inv_cancel]
  refine ⟨normalElement, ⟨normal_member,
    (Subgroup.normalizer (subgroup : Set GroupType)).mul_mem normalized
      ((Subgroup.normalizer (subgroup : Set GroupType)).inv_mem supplement_normalized)⟩,
    representative.val, ⟨representative.property, supplement_normalized⟩, ?_⟩
  change element * representative.val⁻¹ * representative.val = element
  rw [mul_assoc, inv_mul_cancel, mul_one]

theorem normalizer_sup_coprime_kernel (prime : ℕ) (prime_prime : prime.Prime)
    (normal supplement subgroup : Subgroup GroupType) [normal.Normal]
    (normal_coprime : Nat.Coprime prime (Nat.card normal))
    (whole : normal ⊔ supplement = ⊤) (contained : subgroup ≤ supplement)
    (pgroup : IsPGroup prime subgroup) :
    Subgroup.normalizer (subgroup : Set GroupType) =
      (normal ⊓ Subgroup.normalizer (subgroup : Set GroupType)) ⊔
        (supplement ⊓ Subgroup.normalizer (subgroup : Set GroupType)) := by
  apply le_antisymm
  · intro element member
    obtain ⟨normalElement, normal_member, supplementElement, supplement_member, product_eq⟩ :=
      normalizer_product_coprime_kernel prime prime_prime normal supplement subgroup
        normal_coprime whole contained pgroup element member
    rw [← product_eq]
    exact (normal ⊓ Subgroup.normalizer (subgroup : Set GroupType) ⊔
      supplement ⊓ Subgroup.normalizer (subgroup : Set GroupType)).mul_mem
        (Subgroup.mem_sup_left normal_member) (Subgroup.mem_sup_right supplement_member)
  · exact sup_le inf_le_right inf_le_right

theorem ambient_normalizer_sup_coprime_kernel (prime : ℕ) (prime_prime : prime.Prime)
    (parent normal supplement subgroup : Subgroup GroupType)
    (normal_le : normal ≤ parent) (supplement_le : supplement ≤ parent)
    (internal_normal : (normal.subgroupOf parent).Normal)
    (normal_coprime : Nat.Coprime prime (Nat.card normal))
    (whole : normal ⊔ supplement = parent) (contained : subgroup ≤ supplement)
    (pgroup : IsPGroup prime subgroup) :
    parent ⊓ Subgroup.normalizer (subgroup : Set GroupType) =
      (normal ⊓ Subgroup.normalizer (subgroup : Set GroupType)) ⊔
        (supplement ⊓ Subgroup.normalizer (subgroup : Set GroupType)) := by
  let := internal_normal
  have subgroup_le := contained.trans supplement_le
  have internal_coprime : Nat.Coprime prime (Nat.card (normal.subgroupOf parent)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe normal_le).toEquiv]
    exact normal_coprime
  have internal_whole : normal.subgroupOf parent ⊔ supplement.subgroupOf parent = ⊤ := by
    rw [← Subgroup.subgroupOf_sup normal_le supplement_le, whole, Subgroup.subgroupOf_self]
  have internal_contained : subgroup.subgroupOf parent ≤ supplement.subgroupOf parent :=
    Subgroup.comap_mono contained
  have internal_pgroup : IsPGroup prime (subgroup.subgroupOf parent) :=
    pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe subgroup_le).symm
  have internal_eq := normalizer_sup_coprime_kernel prime prime_prime
    (normal.subgroupOf parent) (supplement.subgroupOf parent) (subgroup.subgroupOf parent)
    internal_coprime internal_whole internal_contained internal_pgroup
  have mapped_eq := congrArg (Subgroup.map parent.subtype) internal_eq
  rw [normalizer_subgroupOf_map parent subgroup subgroup_le, Subgroup.map_sup,
    Subgroup.map_inf _ _ _ parent.subtype_injective,
    Subgroup.map_inf _ _ _ parent.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le normal_le,
    Subgroup.map_subgroupOf_eq_of_le supplement_le,
    normalizer_subgroupOf_map parent subgroup subgroup_le] at mapped_eq
  simpa only [← inf_assoc, inf_eq_left.mpr normal_le, inf_eq_left.mpr supplement_le] using mapped_eq

end CFSG.SignalizerFunctor.Helpers
