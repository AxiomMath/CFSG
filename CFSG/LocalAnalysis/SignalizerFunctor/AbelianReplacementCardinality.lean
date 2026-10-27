module

public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductCardinality
public import CFSG.LocalAnalysis.SignalizerFunctor.AbelianReplacementControl

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem abelian_replacement_difference_product (target : Subgroup GroupType) (conjugator : GroupType)
    (normalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType)) :
    subgroupProduct target (abelianReplacementDifferences target conjugator) =
      ((target ⊔ conjugateSubgroup conjugator target : Subgroup GroupType) : Set GroupType) := by
  have control := normalizer_conjugate_target_control target conjugator normalizes
  have differences_normalize : abelianReplacementDifferences target conjugator ≤
      Subgroup.normalizer (target : Set GroupType) :=
    (abelian_replacement_difference_le_product target conjugator).trans
      (sup_le Subgroup.le_normalizer control.1)
  ext element
  change (∃ first ∈ target, ∃ second ∈ abelianReplacementDifferences target conjugator,
    first * second = element) ↔ _
  rw [← mem_sup_of_normalizing target (abelianReplacementDifferences target conjugator)
    differences_normalize element, abelian_replacement_product_generated]
  rfl

theorem abelian_replacement_eq_intersection_normal_product (target normal : Subgroup GroupType)
    [normal.Normal] (derived_le : ⁅normal, normal⁆ ≤ target) (conjugator : GroupType)
    (member : conjugator ∈ normal)
    (normalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType)) :
    abelianReplacement target conjugator = abelianReplacementIntersection target conjugator ⊔
      ((target ⊔ conjugateSubgroup conjugator target) ⊓ normal) := by
  let parent := target ⊔ conjugateSubgroup conjugator target
  let intersection := abelianReplacementIntersection target conjugator
  let differences := abelianReplacementDifferences target conjugator
  have difference_le := abelian_replacement_difference_le_product target conjugator
  have difference_normal := abelian_replacement_difference_le_normal target normal conjugator member
  have whole := abelian_replacement_difference_product target conjugator normalizes
  have old_intersection_le := abelian_replacement_intersection_contains_normal target normal derived_le
    conjugator member
  change intersection ⊔ differences = intersection ⊔ (parent ⊓ normal)
  apply le_antisymm (sup_le_sup le_rfl (le_inf difference_le difference_normal))
  apply sup_le le_sup_left
  intro element element_member
  have decomposable : element ∈ subgroupProduct target differences := by rw [whole]; exact element_member.1
  obtain ⟨first, first_member, second, second_member, product⟩ := decomposable
  have first_normal : first ∈ normal := by
    have cancelled := normal.mul_mem element_member.2 (normal.inv_mem (difference_normal second_member))
    rw [← product, mul_assoc, mul_inv_cancel, mul_one] at cancelled
    exact cancelled
  rw [← product]
  exact (intersection ⊔ differences).mul_mem
    (Subgroup.mem_sup_left (old_intersection_le ⟨first_member, first_normal⟩))
    (Subgroup.mem_sup_right second_member)

theorem abelian_replacement_intersection_eq (target normal : Subgroup GroupType) [normal.Normal]
    (derived_le : ⁅normal, normal⁆ ≤ target) (conjugator : GroupType) (member : conjugator ∈ normal)
    (abelian : IsMulCommutative target)
    (normalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType)) :
    target ⊓ abelianReplacement target conjugator = abelianReplacementIntersection target conjugator := by
  let intersection := abelianReplacementIntersection target conjugator
  let differences := abelianReplacementDifferences target conjugator
  let parent := target ⊔ conjugateSubgroup conjugator target
  have control := normalizer_conjugate_abelian_product_control target abelian conjugator normalizes
  have differences_le := abelian_replacement_difference_le_product target conjugator
  have difference_normal := abelian_replacement_difference_le_normal target normal conjugator member
  have old_intersection_le := abelian_replacement_intersection_contains_normal target normal derived_le
    conjugator member
  have differences_normalize : differences ≤ Subgroup.normalizer (intersection : Set GroupType) := by
    exact (differences_le.trans (Subgroup.le_centralizer_iff.mp control.2.2.2)).trans
      (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm
  · intro element element_member
    obtain ⟨first, first_member, second, second_member, product⟩ :=
      (mem_sup_of_normalizing intersection differences differences_normalize element).mp element_member.2
    have second_target : second ∈ target := by
      have cancelled := target.mul_mem (target.inv_mem first_member.1) element_member.1
      rw [← product, ← mul_assoc, inv_mul_cancel, one_mul] at cancelled
      exact cancelled
    rw [← product]
    exact intersection.mul_mem first_member (old_intersection_le ⟨second_target, difference_normal second_member⟩)
  · exact le_inf inf_le_left le_sup_left

theorem abelian_replacement_product (target : Subgroup GroupType) (abelian : IsMulCommutative target)
    (conjugator : GroupType)
    (normalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType)) :
    subgroupProduct target (abelianReplacement target conjugator) =
      ((target ⊔ conjugateSubgroup conjugator target : Subgroup GroupType) : Set GroupType) := by
  have control := normalizer_conjugate_abelian_product_control target abelian conjugator normalizes
  have replacement_le : abelianReplacement target conjugator ≤ target ⊔ conjugateSubgroup conjugator target :=
    sup_le (inf_le_left.trans le_sup_left) (abelian_replacement_difference_le_product target conjugator)
  have replacement_normalizes := replacement_le.trans control.1
  have generation : target ⊔ abelianReplacement target conjugator = target ⊔ conjugateSubgroup conjugator target := by
    change target ⊔ (abelianReplacementIntersection target conjugator ⊔
      abelianReplacementDifferences target conjugator) = _
    rw [← sup_assoc target (abelianReplacementIntersection target conjugator),
      sup_eq_left.mpr (show abelianReplacementIntersection target conjugator ≤ target from inf_le_left),
      abelian_replacement_product_generated]
  ext element
  change (∃ first ∈ target, ∃ second ∈ abelianReplacement target conjugator, first * second = element) ↔ _
  rw [← mem_sup_of_normalizing target (abelianReplacement target conjugator) replacement_normalizes element,
    generation]
  rfl

variable [Finite GroupType]

theorem abelian_replacement_card (target normal : Subgroup GroupType) [normal.Normal]
    (derived_le : ⁅normal, normal⁆ ≤ target) (conjugator : GroupType) (member : conjugator ∈ normal)
    (abelian : IsMulCommutative target)
    (normalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType)) :
    Nat.card (abelianReplacement target conjugator) = Nat.card target := by
  have control := normalizer_conjugate_target_control target conjugator normalizes
  have conjugate_product : subgroupProduct target (conjugateSubgroup conjugator target) =
      ((target ⊔ conjugateSubgroup conjugator target : Subgroup GroupType) : Set GroupType) := by
    ext element
    change (∃ first ∈ target, ∃ second ∈ conjugateSubgroup conjugator target, first * second = element) ↔ _
    exact (mem_sup_of_normalizing target _ control.1 element).symm
  have first_card := subgroup_product_cardinality target (conjugateSubgroup conjugator target)
  have second_card := subgroup_product_cardinality target (abelianReplacement target conjugator)
  rw [conjugate_product, conjugate_subgroup_card] at first_card
  rw [abelian_replacement_product target abelian conjugator normalizes,
    abelian_replacement_intersection_eq target normal derived_le conjugator member abelian normalizes] at second_card
  exact (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := target)) (second_card.trans first_card.symm))

end CFSG.SignalizerFunctor.Helpers
