module

public import CFSG.Permutation.FiveTransitive.SymmetricCommutatorSupport
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.ManningFamilyInequality

open Equiv
open scoped BigOperators commutatorElement

theorem sum_minimum_add_edges_le
    {T X : Type*} [Fintype T] [Fintype X] [DecidableEq X]
    (g : Perm X) (v : T → Perm X) (m : ℕ) (e : T → ℕ)
    (hmin : ∀ t, m + e t ≤ ⁅g, v t⁆.support.card) :
    Nat.card T * m + (∑ t, e t) +
      (∑ t, ((g.support ∩ (v t).support).filter (fun x => g x ∈ g.support ∩ (v t).support)).card) +
      (∑ t, ((g.support ∩ (v t).support).filter (fun x => v t x ∈ g.support ∩ (v t).support)).card) ≤
      3 * (∑ t, (g.support ∩ (v t).support).card) := by
  classical
  have hpoint (t : T) := SymmetricCommutatorSupport.card_support_commutator_add_edges_le g (v t)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ =>
    (show m + e t +
      ((g.support ∩ (v t).support).filter (fun x => g x ∈ g.support ∩ (v t).support)).card +
      ((g.support ∩ (v t).support).filter (fun x => v t x ∈ g.support ∩ (v t).support)).card ≤
      3 * (g.support ∩ (v t).support).card from by
        have hp := hpoint t
        dsimp only at hp
        have hl := hmin t
        omega))
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card, Finset.mul_sum] using hsum

theorem cleared_inequality
    (n m Q Isum qsum rsum Esum j k e : ℕ) (hQpos : 0 < Q)
    (hI : Isum * (n - 3) = Q * (n - 3) + Q * (m - 1) * (m - 3))
    (hq : qsum * (n - 3) * (n - 4) =
      Q * k * (m - 1) * (n - 4) + Q * j * (m - 1) * (m - 2))
    (hr : rsum * (n - 3) * (n - 4) =
      2 * Q * (m - 3) * (n - 4) + Q * (m - 2) * (m - 3) * (m - 4))
    (he : Esum * (n - 3) * (n - 4) = Q * e)
    (hsum : Q * m + Esum + qsum + rsum ≤ 3 * Isum) :
    m * (n - 3) * (n - 4) + e +
      2 * (m - 3) * (n - 4) + (m - 2) * (m - 3) * (m - 4) +
      k * (m - 1) * (n - 4) + j * (m - 1) * (m - 2) ≤
      3 * (n - 3) * (n - 4) + 3 * (m - 1) * (m - 3) * (n - 4) := by
  have hmul := Nat.mul_le_mul_right ((n - 3) * (n - 4)) hsum
  have hIL := congrArg (fun x : ℕ => x * (n - 4)) hI
  have hleft : (Q * m + Esum + qsum + rsum) * ((n - 3) * (n - 4)) =
      Q * (m * (n - 3) * (n - 4) + e +
        2 * (m - 3) * (n - 4) + (m - 2) * (m - 3) * (m - 4) +
        k * (m - 1) * (n - 4) + j * (m - 1) * (m - 2)) := by
    calc
      _ = Q * m * (n - 3) * (n - 4) +
          Esum * (n - 3) * (n - 4) + qsum * (n - 3) * (n - 4) +
          rsum * (n - 3) * (n - 4) := by ring
      _ = _ := by rw [he, hq, hr]; ring
  have hright : (3 * Isum) * ((n - 3) * (n - 4)) =
      Q * (3 * (n - 3) * (n - 4) + 3 * (m - 1) * (m - 3) * (n - 4)) := by
    calc
      _ = 3 * (Isum * (n - 3) * (n - 4)) := by ring
      _ = _ := by rw [hIL]; ring
  rw [hleft, hright] at hmul
  exact Nat.le_of_mul_le_mul_left hmul hQpos

end FiveTransitive.ManningFamilyInequality

end CFSG
