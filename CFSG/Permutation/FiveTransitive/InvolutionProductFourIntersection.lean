module

public import CFSG.Permutation.FiveTransitive.InvolutionProductSupport
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG

namespace FiveTransitive.InvolutionProductFourIntersection
open Equiv

private theorem exists_involution_support_le
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (s t : Perm X) (hsP : s ∈ P) (htP : t ∈ P)
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hfour : 4 ∣ orderOf (s * t)) :
    ∃ w : Perm X, w ∈ P ∧ orderOf w = 2 ∧
      w.support.card ≤ 2 * (s.support ∩ t.support).card := by
  let w := (s * t) ^ (orderOf (s * t) / 2)
  have htwo : 2 ∣ orderOf (s * t) := (show 2 ∣ 4 by decide).trans hfour
  have hw : orderOf w = 2 := orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos (s * t))) htwo
  have hwSquare : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  obtain ⟨k, hk⟩ := hfour
  have hexp : orderOf (s * t) / 2 = 2 * k := by omega
  have hbound := InvolutionProductSupport.card_support_even_power_le s t hs ht k
    (by simpa only [w, hexp] using hwSquare)
  exact ⟨w, P.pow_mem (P.mul_mem hsP htP) _, hw, by simpa only [w, hexp] using hbound⟩

theorem minimum_support_le_twice_intersection
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (m : ℕ)
    (hmin : ∀ g ∈ P, g ≠ 1 → m ≤ (g : Perm X).support.card)
    (s t : Perm X) (hsP : s ∈ P) (htP : t ∈ P)
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hfour : 4 ∣ orderOf (s * t)) :
    m ≤ 2 * (s.support ∩ t.support).card := by
  obtain ⟨w, hwP, hwOrder, hwSupport⟩ := exists_involution_support_le P s t hsP htP hs ht hfour
  have hwne : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hwOrder
    omega
  exact (hmin w hwP hwne).trans hwSupport

end FiveTransitive.InvolutionProductFourIntersection

end CFSG
