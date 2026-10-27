module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallTransport

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem complement_restriction (normal complement parent : Subgroup GroupType) [normal.Normal]
    (complementary : normal.IsComplement' complement) (normal_le : normal ≤ parent) :
    (normal.subgroupOf parent).IsComplement' (complement.subgroupOf parent) := by
  let : (normal.subgroupOf parent).Normal := inferInstance
  apply complement_of_normal_sup_disjoint
  · apply top_unique
    intro element _
    have member : element.val ∈ normal ⊔ complement := by
      rw [complementary.sup_eq_top]
      trivial
    obtain ⟨normalElement, normal_member, complementElement, complement_member, product⟩ :=
      Subgroup.mem_sup_of_normal_left.mp member
    have complement_parent : complementElement ∈ parent := by
      have equality : complementElement = normalElement⁻¹ * element.val := by
        rw [← product]
        group
      rw [equality]
      exact parent.mul_mem (parent.inv_mem (normal_le normal_member)) element.property
    have internal_product : (⟨normalElement, normal_le normal_member⟩ : parent) *
        (⟨complementElement, complement_parent⟩ : parent) = element := Subtype.ext product
    rw [← internal_product]
    exact (normal.subgroupOf parent ⊔ complement.subgroupOf parent).mul_mem
      (Subgroup.mem_sup_left normal_member) (Subgroup.mem_sup_right complement_member)
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro element member
    have ambient_member : element.val ∈ normal ⊓ complement := member
    rw [complementary.disjoint.eq_bot] at ambient_member
    exact Subtype.ext ambient_member

theorem normal_subgroupOf_sup_complement (normal other : Subgroup GroupType) [normal.Normal]
    (disjoint : Disjoint normal other) :
    (normal.subgroupOf (normal ⊔ other)).IsComplement' (other.subgroupOf (normal ⊔ other)) := by
  let : (normal.subgroupOf (normal ⊔ other)).Normal := inferInstance
  apply complement_of_normal_sup_disjoint
  · rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self _
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro element member
    have ambient_member : element.val ∈ normal ⊓ other := member
    rw [disjoint.eq_bot] at ambient_member
    exact Subtype.ext ambient_member

theorem commutative_subgroupOf (parent normal : Subgroup GroupType)
    (commutative : IsMulCommutative normal) : IsMulCommutative (normal.subgroupOf parent) := by
  let := commutative
  apply isMulCommutative_iff.mpr
  intro first second
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun element : normal => (element : GroupType))
    (mul_comm' (⟨first.val.val, first.property⟩ : normal)
      (⟨second.val.val, second.property⟩ : normal))

end CFSG.SignalizerFunctor.Helpers
