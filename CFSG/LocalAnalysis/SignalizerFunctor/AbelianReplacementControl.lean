module

public import CFSG.LocalAnalysis.SignalizerFunctor.WeakClosureConjugation
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCubicDifferences
public import CFSG.LocalAnalysis.SignalizerFunctor.MutuallyNormalizingAbelianProducts

public section

open scoped commutatorElement

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def abelianReplacementDifferences (target : Subgroup GroupType) (conjugator : GroupType) :
    Subgroup GroupType :=
  Subgroup.closure (Set.range (fun element : target => conjugationDifference conjugator element.val))

@[expose] def abelianReplacementIntersection (target : Subgroup GroupType) (conjugator : GroupType) :
    Subgroup GroupType := target ⊓ conjugateSubgroup conjugator target

@[expose] def abelianReplacement (target : Subgroup GroupType) (conjugator : GroupType) : Subgroup GroupType :=
  abelianReplacementIntersection target conjugator ⊔ abelianReplacementDifferences target conjugator

theorem normalizer_conjugate_target_control (target : Subgroup GroupType) (conjugator : GroupType)
    (normalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType)) :
    conjugateSubgroup conjugator target ≤ Subgroup.normalizer (target : Set GroupType) ∧
      Subgroup.normalizer (target : Set GroupType) ≤
        Subgroup.normalizer (conjugateSubgroup conjugator target : Set GroupType) := by
  have conjugates_normalizer : conjugateSubgroup conjugator (Subgroup.normalizer (target : Set GroupType)) =
      Subgroup.normalizer (target : Set GroupType) := Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes
  refine ⟨?_, ?_⟩
  · exact (Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) Subgroup.le_normalizer).trans
      conjugates_normalizer.le
  · rw [← conjugates_normalizer]
    exact conjugate_subgroup_normalizes _ target conjugator le_rfl

theorem normalizer_conjugate_abelian_product_control (target : Subgroup GroupType)
    (abelian : IsMulCommutative target) (conjugator : GroupType)
    (normalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType)) :
    let conjugated := conjugateSubgroup conjugator target
    let parent := target ⊔ conjugated
    parent ≤ Subgroup.normalizer (target : Set GroupType) ∧
      Subgroup.normalizer (target : Set GroupType) ≤ Subgroup.normalizer (parent : Set GroupType) ∧
      ⁅parent, parent⁆ ≤ target ⊓ conjugated ∧
      target ⊓ conjugated ≤ Subgroup.centralizer (parent : Set GroupType) := by
  let := abelian
  have conjugated_abelian : IsMulCommutative (conjugateSubgroup conjugator target) :=
    Subgroup.map_isMulCommutative target (MulAut.conj conjugator).toMonoidHom
  have control := normalizer_conjugate_target_control target conjugator normalizes
  have target_normalizes := Subgroup.le_normalizer.trans control.2
  exact ⟨sup_le Subgroup.le_normalizer control.1,
    (le_inf le_rfl control.2).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _),
    mutually_normalizing_abelian_product_derived target _ abelian conjugated_abelian target_normalizes control.1,
    mutually_normalizing_abelian_intersection_central target _ abelian conjugated_abelian⟩

theorem abelian_replacement_difference_le_product (target : Subgroup GroupType) (conjugator : GroupType) :
    abelianReplacementDifferences target conjugator ≤ target ⊔ conjugateSubgroup conjugator target := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨element, rfl⟩
  unfold conjugationDifference
  change element.val⁻¹ * conjugator * element.val * conjugator⁻¹ ∈ target ⊔ conjugateSubgroup conjugator target
  rw [mul_assoc element.val⁻¹ conjugator element.val, mul_assoc]
  exact (target ⊔ conjugateSubgroup conjugator target).mul_mem
    (Subgroup.mem_sup_left (target.inv_mem element.property))
    (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem (MulAut.conj conjugator).toMonoidHom element.property))

theorem abelian_replacement_difference_le_normal (target normal : Subgroup GroupType) [normal.Normal]
    (conjugator : GroupType) (member : conjugator ∈ normal) :
    abelianReplacementDifferences target conjugator ≤ normal := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨element, rfl⟩
  change element.val⁻¹ * conjugator * element.val * conjugator⁻¹ ∈ normal
  have conjugated : element.val⁻¹ * conjugator * (element.val⁻¹)⁻¹ ∈ normal :=
    Subgroup.Normal.conj_mem inferInstance conjugator member element.val⁻¹
  have contained := normal.mul_mem conjugated (normal.inv_mem member)
  simpa only [inv_inv] using contained

theorem abelian_replacement_product_generated (target : Subgroup GroupType) (conjugator : GroupType) :
    target ⊔ abelianReplacementDifferences target conjugator = target ⊔ conjugateSubgroup conjugator target := by
  apply le_antisymm (sup_le le_sup_left (abelian_replacement_difference_le_product target conjugator))
  apply sup_le le_sup_left
  rintro _ ⟨element, member, rfl⟩
  have difference_member : conjugationDifference conjugator element ∈
      abelianReplacementDifferences target conjugator :=
    Subgroup.subset_closure ⟨⟨element, member⟩, rfl⟩
  have product := (target ⊔ abelianReplacementDifferences target conjugator).mul_mem
    (Subgroup.mem_sup_left member) (Subgroup.mem_sup_right difference_member)
  change conjugator * element * conjugator⁻¹ ∈ target ⊔ abelianReplacementDifferences target conjugator
  simpa only [conjugationDifference, ← mul_assoc, mul_inv_cancel, one_mul] using product

theorem abelian_intersection_normalized_of_derived_le (target normal : Subgroup GroupType)
    (derived_le : ⁅normal, normal⁆ ≤ target) :
    normal ≤ Subgroup.normalizer ((target ⊓ normal : Subgroup GroupType) : Set GroupType) := by
  apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
  apply le_inf
  · exact (Subgroup.commutator_mono inf_le_right le_rfl).trans derived_le
  · exact (Subgroup.commutator_mono inf_le_right le_rfl).trans (Subgroup.commutator_le_self normal)

theorem abelian_replacement_intersection_contains_normal (target normal : Subgroup GroupType)
    (derived_le : ⁅normal, normal⁆ ≤ target) (conjugator : GroupType) (member : conjugator ∈ normal) :
    target ⊓ normal ≤ abelianReplacementIntersection target conjugator := by
  have normalized := abelian_intersection_normalized_of_derived_le target normal derived_le
  intro element element_member
  refine ⟨element_member.1, ?_⟩
  have inverse_member := Subgroup.le_normalizer_iff.mp normalized conjugator⁻¹ (normal.inv_mem member)
    element element_member
  refine ⟨conjugator⁻¹ * element * conjugator, ?_, ?_⟩
  · change conjugator⁻¹ * element * conjugator ∈ target
    have contained : conjugator⁻¹ * element * (conjugator⁻¹)⁻¹ ∈ target := inverse_member.1
    simpa only [inv_inv] using contained
  · change conjugator * (conjugator⁻¹ * element * conjugator) * conjugator⁻¹ = element
    group

end CFSG.SignalizerFunctor.Helpers
