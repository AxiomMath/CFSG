module

public import CFSG.Permutation.FiveTransitive.OddPowerCycleRoots
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG

namespace FiveTransitive.TwoPowerPeriodWitness

open Equiv Function CyclePatternRoots OddPowerCycleRoots

variable {X : Type*}

private theorem exists_full_two_period (g : Perm X) (k : ℕ) (ho : orderOf g = 2 ^ (k + 1)) :
    ∃ x : X, minimalPeriod g x = 2 ^ (k + 1) := by
  have hne : g ^ (2 ^ k) ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ho] at hd
    have hl : 2 ^ k < 2 ^ (k + 1) := by
      rw [pow_succ]
      have := Nat.two_pow_pos k
      omega
    exact Nat.not_dvd_of_pos_of_lt (Nat.two_pow_pos k) hl hd
  obtain ⟨x,hx⟩ : ∃ x : X, (g ^ (2 ^ k)) x ≠ x := by
    by_contra! h
    apply hne
    ext x
    exact h x
  have hn : ¬ IsPeriodicPt g (2 ^ k) x := by
    simpa only [IsPeriodicPt, IsFixedPt, g.iterate_eq_pow] using hx
  have hp : IsPeriodicPt g (2 ^ (k + 1)) x := by
    change g^[2 ^ (k + 1)] x = x
    rw [g.iterate_eq_pow, ← ho, pow_orderOf_eq_one]
    rfl
  exact ⟨x, minimalPeriod_eq_prime_pow hn hp⟩

theorem four_card_pos_of_order_four [Finite X] (g : Perm X) (ho : orderOf g = 4) :
    0 < Nat.card (FourRoot g) := by
  obtain ⟨x,hx⟩ := exists_full_two_period g 1 ho
  apply Finite.card_pos_iff.mpr
  exact ⟨⟨x,(four_root_iff g x).mpr hx⟩⟩

end FiveTransitive.TwoPowerPeriodWitness

end CFSG
