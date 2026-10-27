module

public import CFSG.Foundations.MaxCardThompson
public import CFSG.Foundations.MaxOrderThompsonDefs
import CFSG.Foundations.MaxOrderThompson
public import CFSG.Open.LocalVocabulary

public section

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType] [Finite ImageType]

@[expose, reducible] def maximumOrderAbelianFamily (GroupType : Type groupUniverse) [Group GroupType] :
    Set (Subgroup GroupType) :=
  {target | CFSG.IsMaxCardAbelian target}

theorem maximum_order_abelian_family_nonempty : (maximumOrderAbelianFamily GroupType).Nonempty := by
  obtain ⟨target, member⟩ := CFSG.maxOrderAbelianFamily_nonempty (G := GroupType)
  exact ⟨target, CFSG.isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mpr member⟩

@[expose, reducible] noncomputable def maximumAbelianOrder (GroupType : Type groupUniverse)
    [Group GroupType] [Finite GroupType] : ℕ :=
  CFSG.maxAbelianOrder GroupType

@[expose, reducible] def orderThompsonSubgroup (GroupType : Type groupUniverse) [Group GroupType] :
    Subgroup GroupType :=
  CFSG.maxCardThompson GroupType

@[expose, reducible] def orderThompsonCenter (GroupType : Type groupUniverse) [Group GroupType] :
    Subgroup GroupType :=
  CFSG.maxCardZJ GroupType

omit [Finite GroupType] in
private theorem orderThompsonSubgroup_eq_canonical (GroupType : Type groupUniverse) [Group GroupType] :
    orderThompsonSubgroup GroupType = CFSG.maxCardThompson GroupType :=
  rfl

omit [Finite GroupType] in
private theorem orderThompsonCenter_eq_canonical (GroupType : Type groupUniverse) [Group GroupType] :
    orderThompsonCenter GroupType = CFSG.maxCardZJ GroupType :=
  rfl

theorem maximum_order_abelian_family_iff (target : Subgroup GroupType) :
    target ∈ maximumOrderAbelianFamily GroupType ↔
      IsMulCommutative target ∧ Nat.card target = maximumAbelianOrder GroupType :=
  CFSG.isMaxCardAbelian_iff_mem_maxOrderAbelianFamily

omit [Finite GroupType] [Finite ImageType] in
theorem maximum_order_abelian_family_map (equivalence : GroupType ≃* ImageType)
    (target : Subgroup GroupType) (member : target ∈ maximumOrderAbelianFamily GroupType) :
    target.map equivalence.toMonoidHom ∈ maximumOrderAbelianFamily ImageType :=
  CFSG.IsMaxCardAbelian.map_mulEquiv equivalence member

theorem maximum_abelian_order_equiv (equivalence : GroupType ≃* ImageType) :
    maximumAbelianOrder GroupType = maximumAbelianOrder ImageType :=
  CFSG.maxAbelianOrder_eq_of_mulEquiv equivalence

omit [Finite GroupType] [Finite ImageType] in
theorem order_thompson_subgroup_map_le (equivalence : GroupType ≃* ImageType) :
    (orderThompsonSubgroup GroupType).map equivalence.toMonoidHom ≤ orderThompsonSubgroup ImageType := by
  rw [orderThompsonSubgroup_eq_canonical, orderThompsonSubgroup_eq_canonical]
  exact CFSG.maxCardThompson_map_le equivalence

omit [Finite GroupType] [Finite ImageType] in
theorem order_thompson_subgroup_map (equivalence : GroupType ≃* ImageType) :
    (orderThompsonSubgroup GroupType).map equivalence.toMonoidHom = orderThompsonSubgroup ImageType := by
  rw [orderThompsonSubgroup_eq_canonical, orderThompsonSubgroup_eq_canonical]
  exact CFSG.maxCardThompson_map_mulEquiv equivalence

omit [Finite GroupType] in
theorem order_thompson_subgroup_characteristic : (orderThompsonSubgroup GroupType).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  exact order_thompson_subgroup_map

omit [Finite GroupType] in
theorem embedded_center_eq_inf_centralizer (target : Subgroup GroupType) :
    (Subgroup.center target).map target.subtype = target ⊓ Subgroup.centralizer (target : Set GroupType) :=
  CFSG.center_map_subtype_eq_inf_centralizer target

omit [Finite GroupType] [Finite ImageType] in
theorem order_thompson_center_map (equivalence : GroupType ≃* ImageType) :
    (orderThompsonCenter GroupType).map equivalence.toMonoidHom = orderThompsonCenter ImageType := by
  rw [orderThompsonCenter_eq_canonical, orderThompsonCenter_eq_canonical]
  exact CFSG.maxCardZJ_map_mulEquiv equivalence

omit [Finite GroupType] in
theorem order_thompson_center_characteristic : (orderThompsonCenter GroupType).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  exact order_thompson_center_map

end CFSG.SignalizerFunctor.Helpers
