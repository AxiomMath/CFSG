module

public import CFSG.Permutation.FiveTransitive.RefinedCommutatorSupport
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG

namespace FiveTransitive.RefinedCommutatorMinimalSupport

open Equiv
open scoped commutatorElement

theorem bound_of_fixed_moved_image
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (g h : Perm X) (hg : g ∈ P) (hh : h ∈ P)
    (hminimal : ∀ u : Perm X, u ∈ P → u ≠ 1 → g.support.card ≤ u.support.card)
    (x : X) (hfix : h x = x) (hmove : h (g x) ≠ g x) :
    g.support.card ≤ (g.support ∩ h.support).card +
      (RefinedCommutatorSupport.outsideEntry g h).card +
      (RefinedCommutatorSupport.fixedMovedImage g h).card := by
  have hc : ⁅g, h⁆ ∈ P :=
    P.commutator_le_self (Subgroup.commutator_mem_commutator hg hh)
  have hcne : ⁅g, h⁆ ≠ 1 := by
    intro heq
    exact RefinedCommutatorSupport.not_commute_of_fixed_moved_image g h x hfix hmove
      (commutatorElement_eq_one_iff_commute.mp heq)
  exact (hminimal _ hc hcne).trans
    (RefinedCommutatorSupport.card_support_commutator_le g h)

end FiveTransitive.RefinedCommutatorMinimalSupport

end CFSG
