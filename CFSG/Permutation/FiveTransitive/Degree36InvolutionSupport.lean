module

public import CFSG.Permutation.FiveTransitive.EvenInvolutionProductIntersection
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree36InvolutionSupport

open Equiv MulAction

private theorem support_twenty_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Perm X) (hsP : s ∈ P) (hs : orderOf s = 2) :
    20 ≤ s.support.card := by
  have hne : s ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hs
    omega
  have hmin (g : Perm X) (hgP : g ∈ P) (hg : g ≠ 1) : 18 ≤ g.support.card := by
    have hh := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt hgP hg
    rw [hcard] at hh
    omega
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have hseven := Perm.two_dvd_card_support hs2
  have hslo := hmin s hsP hne
  by_contra hn
  have hs18 : s.support.card = 18 := by omega
  have hfixedcard : (fixedBy X s).ncard = 18 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (Function.fixedPoints s) = _
    rw [Nat.card_eq_fintype_card,Perm.card_fixedPoints,Perm.sum_cycleType,hcard,hs18]
  obtain ⟨t,htP,_,ht,_,hfour,hi,havg⟩ :=
    InvolutionFourAverage.exists_conjugate_four_dvd_overlap P h5 s hsP hs
      (by omega) (by omega)
  rw [hcard,hs18] at havg
  have hi9 : (s.support ∩ t.support).card ≤ 9 := by omega
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  obtain ⟨w,hwP,hw,_,hwfour,hwbound⟩ :=
    EvenInvolutionProductIntersection.exists_even_involution_support_le P s t hsP htP hs2 ht2 hfour
  have hwne : w ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hw
    omega
  have hwlo := hmin w hwP hwne
  omega

theorem fixed_card_le_sixteen
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : P) (hs : orderOf s = 2) : Nat.card (fixedBy X s) ≤ 16 := by
  have horder : orderOf s.val = 2 := by simpa only [Subgroup.orderOf_coe] using hs
  have hh := support_twenty_le P hcard h5 hnotAlt s.val s.property horder
  change Nat.card (Function.fixedPoints s.val) ≤ 16
  rw [Nat.card_eq_fintype_card,Perm.card_fixedPoints,Perm.sum_cycleType,hcard]
  omega

end FiveTransitive.Degree36InvolutionSupport

end CFSG
