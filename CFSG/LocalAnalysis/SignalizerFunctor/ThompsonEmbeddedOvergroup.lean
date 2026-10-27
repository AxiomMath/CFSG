module

public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonSubgroupTransport

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem embedded_order_thompson_center_subgroupOf (parent subgroup : Subgroup GroupType)
    (contained : subgroup ≤ parent) :
    (embeddedOrderThompsonCenter (subgroup.subgroupOf parent)).map parent.subtype =
      embeddedOrderThompsonCenter subgroup := by
  let equivalence := Subgroup.subgroupOfEquivOfLe contained
  have natural := order_thompson_center_map equivalence
  have mapped := congrArg (Subgroup.map subgroup.subtype) natural
  rw [Subgroup.map_map] at mapped
  unfold embeddedOrderThompsonCenter
  rw [Subgroup.map_map]
  have hom_eq : subgroup.subtype.comp equivalence.toMonoidHom =
      parent.subtype.comp (subgroup.subgroupOf parent).subtype := by
    ext element
    rfl
  rwa [hom_eq] at mapped

theorem embedded_order_thompson_center_overgroup (parent subgroup : Subgroup GroupType)
    (contained : subgroup ≤ parent) (witness : Subgroup parent)
    (witness_member : witness ∈ maximumOrderAbelianFamily parent)
    (witness_le : witness.map parent.subtype ≤ subgroup) :
    embeddedOrderThompsonCenter parent ≤ embeddedOrderThompsonCenter subgroup := by
  have internal_le : witness ≤ subgroup.subgroupOf parent := by
    intro element member
    exact witness_le (Subgroup.mem_map_of_mem parent.subtype member)
  have center_le := order_thompson_center_overgroup (subgroup.subgroupOf parent) witness internal_le
    witness_member
  have mapped_le := Subgroup.map_mono (f := parent.subtype) center_le
  change embeddedOrderThompsonCenter parent ≤
    (embeddedOrderThompsonCenter (subgroup.subgroupOf parent)).map parent.subtype at mapped_le
  rwa [embedded_order_thompson_center_subgroupOf parent subgroup contained] at mapped_le

omit [Finite GroupType] in
theorem embedded_maximum_order_abelian_family_subgroupOf (parent subgroup : Subgroup GroupType)
    (contained : subgroup ≤ parent) (target : Subgroup parent)
    (target_member : target ∈ maximumOrderAbelianFamily parent)
    (target_le : target.map parent.subtype ≤ subgroup) :
    (target.map parent.subtype).subgroupOf subgroup ∈ maximumOrderAbelianFamily subgroup := by
  let := target_member.1
  have internal_le : target ≤ subgroup.subgroupOf parent := by
    intro element member
    exact target_le (Subgroup.mem_map_of_mem parent.subtype member)
  have internal_member := maximum_order_abelian_family_subgroupOf (subgroup.subgroupOf parent) target
    internal_le target_member
  let equivalence := Subgroup.subgroupOfEquivOfLe contained
  have mapped_member := maximum_order_abelian_family_map equivalence (target.subgroupOf (subgroup.subgroupOf parent))
    internal_member
  have equality : (target.subgroupOf (subgroup.subgroupOf parent)).map equivalence.toMonoidHom =
      (target.map parent.subtype).subgroupOf subgroup := by
    ext element
    constructor
    · rintro ⟨original, member, rfl⟩
      exact ⟨original.val, member, rfl⟩
    · rintro ⟨original, member, equal⟩
      refine ⟨⟨⟨element.val, contained element.property⟩, element.property⟩, ?_, ?_⟩
      · have original_eq : original = ⟨element.val, contained element.property⟩ := Subtype.ext equal
        exact original_eq ▸ member
      · apply Subtype.ext
        rfl
  rwa [equality] at mapped_member

end CFSG.SignalizerFunctor.Helpers
