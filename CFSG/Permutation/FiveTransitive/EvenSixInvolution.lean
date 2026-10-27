module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

namespace FiveTransitive.EvenSixInvolution

open Equiv

private theorem fixed_card_eq_two_or_six
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (g : Perm X) (hg : g ^ 2 = 1) (hsign : g.sign = 1) :
    Nat.card (Function.fixedPoints g) = 2 ∨ Nat.card (Function.fixedPoints g) = 6 := by
  have hle : g.support.card ≤ 6 := by simpa only [hX] using Finset.card_le_univ g.support
  have heven := Perm.two_dvd_card_support hg
  have hfixed : Fintype.card (Function.fixedPoints g) = 6 - g.support.card := by
    rw [Perm.card_fixedPoints, g.sum_cycleType, hX]
  have hs := Perm.sign_of_pow_two_eq_one hg
  rw [hsign, hX, hfixed] at hs
  rw [Nat.card_eq_fintype_card, hfixed]
  generalize g.support.card = k at *
  interval_cases k <;> norm_num at *
  have hh := congrArg (fun z : ℤˣ => (z : ℤ)) hs
  norm_num at hh

theorem two_le_fixed_card
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (g : Perm X) (hg : g ^ 2 = 1) (hsign : g.sign = 1) :
    2 ≤ Nat.card (Function.fixedPoints g) := by
  rcases fixed_card_eq_two_or_six hX g hg hsign with h | h <;> omega

theorem fixed_card_eq_two_of_ne_one
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (g : Perm X) (hg : g ^ 2 = 1) (hsign : g.sign = 1) (hne : g ≠ 1) :
    Nat.card (Function.fixedPoints g) = 2 := by
  rcases fixed_card_eq_two_or_six hX g hg hsign with h | h
  · exact h
  · rw [Nat.card_eq_fintype_card, Perm.card_fixedPoints, g.sum_cycleType, hX] at h
    exact (hne (Perm.card_support_eq_zero.mp (by omega))).elim

end FiveTransitive.EvenSixInvolution

end CFSG
