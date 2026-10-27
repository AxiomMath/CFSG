module

public import CFSG.Permutation.FiveTransitive.EvenSixInvolution
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

namespace FiveTransitive.EvenSixFreeFour

open MulAction Equiv

private theorem complement_fixed
    {X:Type*} [Fintype X] [DecidableEq X] (hX:Nat.card X=6)
    (H:Subgroup (Perm X)) (heven:H≤alternatingGroup X)
    (hsq:∀h:H,h*h=1) (O:Set X) (hO:O.ncard=4)
    (hfree:∀h:H,h≠1 → ∀x∈O,h • x≠x) : Oᶜ⊆fixedPoints H X := by
  have hcomp:Oᶜ.ncard=2 := by rw [Set.ncard_compl,hX,hO]
  intro x hx
  rw [mem_fixedPoints]
  intro h
  by_cases hh:h=1
  · rw [hh,one_smul]
  · have hpow:h.val^2=1 := by
      simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using congrArg Subtype.val (hsq h)
    have hcard:2≤Nat.card (Function.fixedPoints h.val) :=
      EvenSixInvolution.two_le_fixed_card (by simpa only [Nat.card_eq_fintype_card] using hX)
        h.val hpow (Perm.mem_alternatingGroup.mp (heven h.property))
    have hsub:Function.fixedPoints h.val⊆Oᶜ := by
      intro z hz hzo
      exact hfree h hh z hzo hz
    have heq:Function.fixedPoints h.val=Oᶜ := by
      apply Set.eq_of_subset_of_ncard_le hsub
      rw [hcomp,←Nat.card_coe_set_eq]
      exact hcard
    change x∈Function.fixedPoints h.val
    rwa [heq]

theorem card_le_two
    {X:Type*} [Fintype X] [DecidableEq X] (hX:Nat.card X=6)
    (J H:Subgroup (Perm X)) (heven:J≤alternatingGroup X) (hHJ:H≤J)
    (hpair:∀s:Set X,s.ncard=2 → Nat.card (fixingSubgroup J s)=2)
    (hsq:∀h:H,h*h=1) (O:Set X) (hO:O.ncard=4)
    (hfree:∀h:H,h≠1 → ∀x∈O,h • x≠x) : Nat.card H≤2 := by
  have hfixed := complement_fixed hX H (hHJ.trans heven) hsq O hO hfree
  let K := H.subgroupOf J
  have hK:K≤fixingSubgroup J Oᶜ := by
    intro h hh
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact mem_fixedPoints.mp (hfixed hx) ⟨h.val,hh⟩
  have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hK)
    (Subgroup.inclusion_injective hK)
  rw [hpair Oᶜ (by rw [Set.ncard_compl,hX,hO])] at hcard
  have he:Nat.card K=Nat.card H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHJ).toEquiv
  rwa [he] at hcard

end FiveTransitive.EvenSixFreeFour

end CFSG
