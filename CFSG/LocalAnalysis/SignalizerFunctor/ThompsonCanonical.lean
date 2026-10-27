module

public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonMaxOrder
public import CFSG.Foundations.MaxOrderThompson

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable (GroupType : Type groupUniverse) [Group GroupType]

theorem maximum_order_abelian_family_eq_setOf_isMaxCardAbelian :
    maximumOrderAbelianFamily GroupType = {A : Subgroup GroupType | CFSG.IsMaxCardAbelian A} :=
  rfl

theorem order_thompson_subgroup_eq_maxCardThompson :
    orderThompsonSubgroup GroupType = CFSG.maxCardThompson GroupType :=
  rfl

theorem order_thompson_center_eq_maxCardZJ :
    orderThompsonCenter GroupType = CFSG.maxCardZJ GroupType :=
  rfl

variable [Finite GroupType]

theorem maximum_order_abelian_family_eq_maxOrderAbelianFamily :
    maximumOrderAbelianFamily GroupType = CFSG.maxOrderAbelianFamily GroupType :=
  CFSG.setOf_isMaxCardAbelian_eq

theorem maximum_abelian_order_eq_maxAbelianOrder :
    maximumAbelianOrder GroupType = CFSG.maxAbelianOrder GroupType :=
  rfl

theorem order_thompson_subgroup_eq_orderThompson :
    orderThompsonSubgroup GroupType = CFSG.orderThompson GroupType :=
  (order_thompson_subgroup_eq_maxCardThompson GroupType).trans CFSG.maxCardThompson_eq_orderThompson

theorem order_thompson_center_eq_orderZJ :
    orderThompsonCenter GroupType = CFSG.orderZJ GroupType :=
  (order_thompson_center_eq_maxCardZJ GroupType).trans CFSG.maxCardZJ_eq_orderZJ

end CFSG.SignalizerFunctor.Helpers
