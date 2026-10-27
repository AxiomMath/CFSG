module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

open CFSG.ABGLocalTools (IsSylowOf)

namespace CFSG.RankThree.PartTwo.Late

theorem item1924_orderOf_conj {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

theorem item1924_cube_conj {G : Type*} [Group G] (k x : G) (hx : x ^ 3 = 1) :
    (k⁻¹ * x * k) ^ 3 = 1 := by
  have h := conj_pow (a := k⁻¹) (b := x) (i := 3)
  rw [inv_inv, hx, mul_one, inv_mul_cancel] at h
  exact h

theorem item1924_zpowers_eq_of_mem {G : Type*} [Group G] [Finite G] {x y : G}
    (hxy : x ∈ Subgroup.zpowers y) (hord : orderOf x = orderOf y) :
    Subgroup.zpowers x = Subgroup.zpowers y :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxy)
    (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hord]))

end CFSG.RankThree.PartTwo.Late
