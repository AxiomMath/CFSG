module

public import CFSG.Permutation.FiveTransitive.InvolutionSupportArithmetic
public import CFSG.Permutation.FiveTransitive.InvolutionFourAverage
public import CFSG.Permutation.FiveTransitive.InvolutionProductFourIntersection

public section

namespace CFSG

namespace FiveTransitive.InvolutionMinimalSupportBound

open Equiv MulAction

theorem degree_le_two_mul_support
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h5 : IsMultiplyPretransitive P X 5)
    (s : Perm X) (hsP : s ∈ P) (hs : orderOf s = 2)
    (hm : 5 ≤ s.support.card)
    (hmin : ∀ g : Perm X, g ∈ P → g ≠ 1 → s.support.card ≤ g.support.card) :
    Fintype.card X ≤ 2 * s.support.card := by
  classical
  by_cases hbound : Fintype.card X ≤ 2 * s.support.card
  · exact hbound
  have hn : 4 ≤ Fintype.card X := hm.trans (Finset.card_le_univ _) |>.trans' (by omega)
  have hfixedcard : (fixedBy X s).ncard = Fintype.card X - s.support.card := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (Function.fixedPoints s) = _
    rw [Nat.card_eq_fintype_card, Perm.card_fixedPoints, Perm.sum_cycleType]
  have hfixed : 2 ≤ (fixedBy X s).ncard := by rw [hfixedcard]; omega
  obtain ⟨t, htP, _, ht, _, hfour, hi, havg⟩ :=
    InvolutionFourAverage.exists_conjugate_four_dvd_overlap P h5 s hsP hs hm hfixed
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hoverlap := InvolutionProductFourIntersection.minimum_support_le_twice_intersection
    P s.support.card hmin s t hsP htP hs2 ht2 hfour
  exact InvolutionSupportArithmetic.degree_le_two_mul_support _ _ _ hn hm hi hoverlap havg

end FiveTransitive.InvolutionMinimalSupportBound

end CFSG
