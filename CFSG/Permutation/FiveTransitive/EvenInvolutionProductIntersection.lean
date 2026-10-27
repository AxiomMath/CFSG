module

public import CFSG.Permutation.FiveTransitive.InvolutionProductSupport
public import CFSG.Permutation.FiveTransitive.SimpleActionEven

public section

namespace CFSG

namespace FiveTransitive.EvenInvolutionProductIntersection

open Equiv

theorem exists_even_involution_support_le
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (s t : Perm X) (hsP : s ∈ P) (htP : t ∈ P)
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hfour : 4 ∣ orderOf (s * t)) :
    ∃ w : Perm X, w ∈ P ∧ orderOf w = 2 ∧ w.sign = 1 ∧
      4 ∣ w.support.card ∧ w.support.card ≤ 2 * (s.support ∩ t.support).card := by
  let w := (s * t) ^ (orderOf (s * t) / 2)
  have htwo : 2 ∣ orderOf (s * t) := (show 2 ∣ 4 by decide).trans hfour
  have hw : orderOf w = 2 := orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos (s * t))) htwo
  have hwSquare : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  obtain ⟨k,hk⟩ := hfour
  have hexp : orderOf (s * t) / 2 = 2 * k := by omega
  have hsign : w.sign = 1 := by
    change Perm.sign ((s * t) ^ (orderOf (s * t) / 2)) = 1
    rw [hexp,map_pow,pow_mul,Int.units_sq,one_pow]
  have hdiv := SimpleActionEven.four_dvd_support_of_even_involution w hwSquare hsign
  have hbound := InvolutionProductSupport.card_support_even_power_le s t hs ht k
    (by simpa only [w,hexp] using hwSquare)
  exact ⟨w,P.pow_mem (P.mul_mem hsP htP) _,hw,hsign,hdiv,
    by simpa only [w,hexp] using hbound⟩

end FiveTransitive.EvenInvolutionProductIntersection

end CFSG
