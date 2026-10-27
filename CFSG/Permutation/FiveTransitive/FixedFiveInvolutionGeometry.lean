module

public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG

namespace FiveTransitive.FixedFiveInvolutionGeometry

open MulAction

theorem mem_fixedBy_smul_of_commute
    {G X : Type*} [Group G] [MulAction G X] (a b : G)
    (hab : a * b = b * a) {x : X} (hx : x ∈ fixedBy X a) :
    b • x ∈ fixedBy X a := by
  change a • (b • x) = b • x
  rw [← mul_smul, hab, mul_smul, hx]

theorem fixedBy_eq_of_five
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (a : G) (hbound : (fixedBy X a).ncard ≤ 5)
    (s : Set X) (hs : s.ncard = 5) (hsub : s ⊆ fixedBy X a) :
    fixedBy X a = s := by
  apply (Set.eq_of_subset_of_ncard_le hsub ?_).symm
  rwa [hs]

theorem mul_square_one
    {G : Type*} [Group G] (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : (a * b) * (a * b) = 1 := by
  calc
    (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

end FiveTransitive.FixedFiveInvolutionGeometry

end CFSG
