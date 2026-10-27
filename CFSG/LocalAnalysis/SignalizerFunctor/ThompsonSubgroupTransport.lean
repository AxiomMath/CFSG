module

public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonCenterIntersection
import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonCanonical

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem maximum_order_abelian_family_subgroupOf (parent target : Subgroup GroupType)
    (contained : target ≤ parent) (member : target ∈ maximumOrderAbelianFamily GroupType) :
    target.subgroupOf parent ∈ maximumOrderAbelianFamily parent :=
  CFSG.IsMaxCardAbelian.subgroupOf member contained

omit [Finite GroupType] in
theorem maximum_order_abelian_family_subgroup_map (parent witness : Subgroup GroupType)
    (contained : witness ≤ parent) (witness_member : witness ∈ maximumOrderAbelianFamily GroupType)
    (candidate : Subgroup parent) (member : candidate ∈ maximumOrderAbelianFamily parent) :
    candidate.map parent.subtype ∈ maximumOrderAbelianFamily GroupType :=
  CFSG.IsMaxCardAbelian.map_subtype witness_member contained member

theorem maximum_abelian_order_subgroup (parent witness : Subgroup GroupType)
    (contained : witness ≤ parent) (member : witness ∈ maximumOrderAbelianFamily GroupType) :
    maximumAbelianOrder parent = maximumAbelianOrder GroupType := by
  rw [maximum_abelian_order_eq_maxAbelianOrder, maximum_abelian_order_eq_maxAbelianOrder]
  exact CFSG.maxAbelianOrder_subgroup_eq
    (CFSG.isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mp member) contained

theorem order_thompson_center_overgroup (parent witness : Subgroup GroupType)
    (contained : witness ≤ parent) (member : witness ∈ maximumOrderAbelianFamily GroupType) :
    orderThompsonCenter GroupType ≤ (orderThompsonCenter parent).map parent.subtype := by
  rw [order_thompson_center_eq_orderZJ, order_thompson_center_eq_orderZJ]
  exact CFSG.orderZJ_le_ambientOrderZJ
    (CFSG.isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mp member) contained

@[expose] def embeddedOrderThompsonCenter (target : Subgroup GroupType) : Subgroup GroupType :=
  (orderThompsonCenter target).map target.subtype

omit [Finite GroupType] in
theorem embedded_order_thompson_center_properties (target actor : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    embeddedOrderThompsonCenter target ≤ target ∧
      IsMulCommutative (embeddedOrderThompsonCenter target) ∧
      actor ≤ Subgroup.normalizer (embeddedOrderThompsonCenter target : Set GroupType) := by
  unfold embeddedOrderThompsonCenter
  rw [order_thompson_center_eq_maxCardZJ]
  exact ⟨Subgroup.map_subtype_le _, inferInstance,
    normalized.trans (CFSG.normalizer_le_normalizer_image_of_characteristic target _)⟩

theorem embedded_order_thompson_center_pgroup (prime : ℕ) (prime_prime : prime.Prime)
    (target : Subgroup GroupType) (pgroup : IsPGroup prime target) (nontrivial : target ≠ ⊥) :
    embeddedOrderThompsonCenter target ≠ ⊥ ∧ IsPGroup prime (embeddedOrderThompsonCenter target) := by
  let _nontrivial : Nontrivial target := (Subgroup.nontrivial_iff_ne_bot target).mpr nontrivial
  refine ⟨?_, (pgroup.to_subgroup (orderThompsonCenter target)).map target.subtype⟩
  intro trivial
  exact order_thompson_center_pgroup_nontrivial prime prime_prime pgroup
    ((Subgroup.map_eq_bot_iff_of_injective _ target.subtype_injective).mp trivial)

end CFSG.SignalizerFunctor.Helpers
