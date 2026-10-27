module

public import CFSG.Permutation.FiveTransitive.ExceptionalThreeCommutator

public section

namespace CFSG

namespace FiveTransitive.ExceptionalThreeSupport

open Equiv
open scoped commutatorElement

theorem support_gt_min_of_exceptional
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (m : ℕ)
    (hmin : ∀ g : Perm X, g ∈ P → g ≠ 1 → m ≤ g.support.card)
    (hno : ∀ g : Perm X, g ∈ P → orderOf g = 2 → g.support.card ≠ m)
    (g v : Perm X) (hgP : g ∈ P) (hvP : v ∈ P)
    {a b c x : X} (hab : a ≠ b) (hac : a ≠ c)
    (ga : g a = b) (gb : g b = c) (gc : g c = a) (gx : g x = x)
    (vb : v b = b)
    (hevent : (v a = c ∧ v c = x ∧ v x = a) ∨
      (v a = x ∧ v x = c ∧ v c = a)) :
    m + 1 ≤ ⁅g, v⁆.support.card := by
  apply ExceptionalThreeCommutator.support_gt_min_of_even_order P m hmin hno
    (P.commutator_le_self (Subgroup.commutator_mem_commutator hgP hvP))
  rcases hevent with ⟨va, vc, vx⟩ | ⟨va, vx, vc⟩
  · obtain ⟨h1, h2⟩ := ExceptionalThreeCommutator.commutator_exchange_first
      g v ga gb gc gx vb va vc vx
    exact ExceptionalThreeCommutator.two_dvd_orderOf_of_exchange _ hab h1 h2
  · obtain ⟨h1, h2⟩ := ExceptionalThreeCommutator.commutator_exchange_second
      g v ga gb gc gx vb va vx vc
    exact ExceptionalThreeCommutator.two_dvd_orderOf_of_exchange _ hac h1 h2

end FiveTransitive.ExceptionalThreeSupport

end CFSG
