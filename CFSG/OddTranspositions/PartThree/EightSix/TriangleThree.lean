module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Solvable

import CFSG.RankThree.GF2n.Tim77.TriangleSolvable

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

theorem isSolvable_closure_of_orderOf_mul_eq_three {X : Type*} [Group X] {u w v : X}
    (hu : u * u = 1) (hw : w * w = 1) (hv : v * v = 1) (huv : Commute u v)
    (huw : orderOf (u * w) = 3) (hvw : orderOf (v * w) = 3) :
    Group.IsSolvable ↥(Subgroup.closure ({u, w, v} : Set X)) := by
  have hwu : w * u = w * (u * w) * w⁻¹ := by group
  have hwv : w * v = w * (v * w) * w⁻¹ := by group
  have hwu3 : (w * u) ^ 3 = 1 := by
    rw [hwu, conj_pow, ← huw, pow_orderOf_eq_one]
    group
  have hwv3 : (w * v) ^ 3 = 1 := by
    rw [hwv, conj_pow, ← hvw, pow_orderOf_eq_one]
    group
  have huv2 : (u * v) ^ 2 = 1 := by
    rw [huv.mul_pow 2]
    simp [pow_two, hu, hv]
  have h : Group.IsSolvable ↥(Subgroup.closure ({w, u, v} : Set X)) :=
    CFSG.RankThree.GF2n.Tim77.isSolvable_closure_of_triangle hw hu hv hwu3 hwv3
      (Or.inr huv2)
  rwa [show ({w, u, v} : Set X) = {u, w, v} by rw [Set.insert_comm w u]] at h

theorem isSolvable_of_orderOf_mul_eq_three {X : Type*} [Group X] {u w v : X}
    (hu : u * u = 1) (hw : w * w = 1) (hv : v * v = 1) (huv : Commute u v)
    (huw : orderOf (u * w) = 3) (hvw : orderOf (v * w) = 3)
    (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤) : Group.IsSolvable X := by
  have htop : Group.IsSolvable ↥(⊤ : Subgroup X) := by
    rw [← hgen]
    exact isSolvable_closure_of_orderOf_mul_eq_three hu hw hv huv huw hvw
  exact @Group.isSolvable_of_surjective ↥(⊤ : Subgroup X) X _ _
    (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom
    (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).surjective htop

end CFSG.OddTranspositions.PartThree.EightSix
