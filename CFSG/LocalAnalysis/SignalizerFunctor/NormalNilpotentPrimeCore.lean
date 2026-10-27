module

public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem normal_nilpotent_prime_subgroup_le_core (prime : ℕ) (prime_prime : prime.Prime)
    (normal target : Subgroup GroupType) [normal.Normal] [Group.IsNilpotent normal]
    (contained : target ≤ normal) (pgroup : IsPGroup prime target) : target ≤ primeSetCore {prime} := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have internal_pgroup : IsPGroup prime (target.subgroupOf normal) :=
    pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe contained).symm
  obtain ⟨sylow, internal_le⟩ := internal_pgroup.exists_le_sylow
  let _characteristic := sylow.characteristic_of_normal inferInstance
  have embedded_normal := normal_of_characteristic_subgroup normal (sylow : Subgroup normal)
  have embedded_le := prime_set_core_contains {prime} ((sylow : Subgroup normal).map normal.subtype)
    embedded_normal ((prime_supported_singleton_iff_pgroup prime prime_prime _).mpr
      (sylow.isPGroup'.map normal.subtype))
  have mapped_le := Subgroup.map_mono (f := normal.subtype) internal_le
  rw [Subgroup.map_subgroupOf_eq_of_le contained] at mapped_le
  exact mapped_le.trans embedded_le

theorem central_kernel_pgroup_image_nilpotent (prime : ℕ) (prime_prime : prime.Prime)
    (parent kernel : Subgroup GroupType)
    (kernel_central : kernel ≤ Subgroup.centralizer (parent : Set GroupType))
    (kernel_normal : kernel.Normal)
    (image_pgroup : IsPGroup prime (parent.map (@QuotientGroup.mk' _ _ kernel kernel_normal))) :
    Group.IsNilpotent parent := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let := kernel_normal
  let projection := QuotientGroup.mk' kernel
  let restricted := subgroupImageHom projection parent
  let _nilpotent := image_pgroup.isNilpotent
  apply Subgroup.isNilpotent_of_ker_le_center restricted
  intro element member
  have image_one : projection element.val = 1 := congrArg Subtype.val member
  have kernel_member := (QuotientGroup.eq_one_iff _).mp image_one
  have central := kernel_central kernel_member
  apply Subgroup.mem_center_iff.mpr
  intro other
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp central other.val other.property

end CFSG.SignalizerFunctor.Helpers
