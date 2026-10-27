module

public import CFSG.Permutation.FiveTransitive.OddPowerTwoCount
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG

namespace FiveTransitive.TwoPartCycleShape

open Equiv Function CyclePatternRoots OddPowerCycleRoots OddPowerTwoCount

variable {X : Type*}

theorem four_dvd_orderOf_of_four_root (g : Perm X)
    (h4 : 0 < Nat.card (FourRoot g)) : 4 ∣ orderOf g := by
  obtain ⟨x⟩ : Nonempty (FourRoot g) := Nat.card_pos_iff.mp h4 |>.1
  have hp : IsPeriodicPt g (orderOf g) x.val := by
    change g^[orderOf g] x.val = x.val
    rw [g.iterate_eq_pow, pow_orderOf_eq_one]
    rfl
  have hd := hp.minimalPeriod_dvd
  rwa [(four_root_iff g x.val).mp x.property] at hd

theorem exists_odd_pow_two_part [Finite X] (g : Perm X)
    (h4 : 0 < Nat.card (FourRoot g)) :
    ∃ t k : ℕ, Odd t ∧ 2 ≤ k ∧ orderOf (g ^ t) = 2 ^ k ∧
      0 < Nat.card (FourRoot (g ^ t)) := by
  obtain ⟨k,t,ht,he⟩ := Nat.exists_eq_two_pow_mul_odd
    (Nat.ne_of_gt (orderOf_pos g))
  have ht0 : t ≠ 0 := by obtain ⟨a,ha⟩ := ht; omega
  have htdvd : t ∣ orderOf g := ⟨2 ^ k, by rw [he, Nat.mul_comm]⟩
  have ho : orderOf (g ^ t) = 2 ^ k := by
    rw [orderOf_pow_of_dvd ht0 htdvd, he]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero ht0)
  have h4t := four_card_pow_pos g ht h4
  have hd := four_dvd_orderOf_of_four_root (g ^ t) h4t
  have hk : 2 ≤ k := by
    rw [ho] at hd
    by_contra hn
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl <;> norm_num at hd
  exact ⟨t,k,ht,hk,ho,h4t⟩

end FiveTransitive.TwoPartCycleShape

end CFSG
