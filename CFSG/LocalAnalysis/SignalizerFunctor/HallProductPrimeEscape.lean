module

public import CFSG.LocalAnalysis.SignalizerFunctor.IncompleteHallProduct

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem product_normal_subgroup_le_overgroup_core (complement factor target control : Subgroup GroupType)
    (whole : subgroupProduct complement factor = Set.univ) (target_le : target ≤ complement)
    (normal : (target.subgroupOf complement).Normal) (target_control : target ≤ control)
    (factor_control : factor ≤ control) : target ≤ control.normalCore := by
  have normalized : complement ≤ Subgroup.normalizer (target : Set GroupType) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer target_le).mp normal
  rw [Subgroup.normalCore_eq_iInf_comap_conj]
  apply le_iInf
  intro conjugator element member
  obtain ⟨complementElement, complement_member, factorElement, factor_member, product⟩ :=
    (subgroup_product_eq_univ_iff complement factor).mp whole conjugator⁻¹
  have conjugator_equal : conjugator = factorElement⁻¹ * complementElement⁻¹ := by
    have inverses := congrArg Inv.inv product
    simpa only [mul_inv_rev, inv_inv] using inverses.symm
  have conjugated_target := Subgroup.le_normalizer_iff.mp normalized complementElement⁻¹
    (complement.inv_mem complement_member) element member
  have product_member := control.mul_mem
    (control.mul_mem (control.inv_mem (factor_control factor_member)) (target_control conjugated_target))
    (factor_control factor_member)
  change conjugator * element * conjugator⁻¹ ∈ control
  rw [conjugator_equal]
  have equal : (factorElement⁻¹ * complementElement⁻¹) * element * (factorElement⁻¹ * complementElement⁻¹)⁻¹ =
      factorElement⁻¹ * (complementElement⁻¹ * element * complementElement) * factorElement := by group
  rw [equal]
  simpa only [inv_inv] using product_member

variable [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_normal_kernel_escape (kernel target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (kernel_le : kernel ≤ complement) (kernel_nontrivial : kernel ≠ ⊥)
    (kernel_normal : (kernel.subgroupOf complement).Normal)
    (target_le : target ≤ parent) (compatible : solvableSignalizerCompatible prime rank actor values target)
    (kernel_target : kernel ≤ target) : ¬ factor ≤ target := by
  intro factor_target
  let control := parent ⊓ Subgroup.normalizer (factor : Set GroupType)
  have control_compatible := incomplete_abelian_hall_product_factor_normalizer_compatible datum abelian
  have factor_normal : (factor.subgroupOf target).Normal :=
    (incomplete_abelian_hall_product_fitting_eq_factor target datum target_le factor_target abelian compatible.2).2
  have target_control : target ≤ control := le_inf target_le
    ((Subgroup.normal_subgroupOf_iff_le_normalizer factor_target).mp factor_normal)
  have kernel_control : kernel ≤ control := kernel_target.trans target_control
  have factor_control : factor ≤ control := le_inf datum.factor_le Subgroup.le_normalizer
  have internal_kernel_le : kernel.subgroupOf parent ≤ complement.subgroupOf parent :=
    Subgroup.comap_mono kernel_le
  have internal_kernel_normal : ((kernel.subgroupOf parent).subgroupOf (complement.subgroupOf parent)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer internal_kernel_le).mpr
    have complement_normalizes : complement ≤ Subgroup.normalizer (kernel : Set GroupType) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer kernel_le).mp kernel_normal
    apply Subgroup.le_normalizer_iff.mpr
    intro conjugator conjugator_member element element_member
    exact Subgroup.le_normalizer_iff.mp complement_normalizes conjugator.val conjugator_member element.val element_member
  have kernel_core : kernel.subgroupOf parent ≤ (control.subgroupOf parent).normalCore :=
    product_normal_subgroup_le_overgroup_core (complement.subgroupOf parent) (factor.subgroupOf parent)
      (kernel.subgroupOf parent) (control.subgroupOf parent)
      (parent_subgroup_product_whole parent complement factor datum.complement_le datum.factor_le datum.whole)
      internal_kernel_le internal_kernel_normal (Subgroup.comap_mono kernel_control) (Subgroup.comap_mono factor_control)
  have core_trivial := incomplete_full_parent_centralizers_compatible_core_trivial prime rank datum.prime_prime
    actor parent control datum.elementary datum.large values (incomplete_hall_product_parent_coprime datum)
    datum.parent_normalized (incomplete_hall_product_full_centralizers datum) datum.locally_complete datum.incomplete
    control_compatible inf_le_left
  rw [core_trivial] at kernel_core
  have internal_trivial : kernel.subgroupOf parent = ⊥ := le_bot_iff.mp kernel_core
  have mapped_trivial := congrArg (Subgroup.map parent.subtype) internal_trivial
  rw [Subgroup.map_subgroupOf_eq_of_le (kernel_le.trans datum.complement_le), Subgroup.map_bot] at mapped_trivial
  exact kernel_nontrivial mapped_trivial

end CFSG.SignalizerFunctor.Helpers
