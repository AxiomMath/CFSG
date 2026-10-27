module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.ASVolI.ChH

open Equiv Equiv.Perm

private theorem cycleType_eq_replicate_two_of_sq_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    {x : Perm α} (hx : x ^ 2 = 1) :
    x.cycleType = Multiset.replicate (Multiset.card x.cycleType) 2 :=
  Multiset.eq_replicate_card.2 ((pow_prime_eq_one_iff (σ := x) (p := 2)).1 hx)

private theorem cycleType_eq_two_two_or_two_two_two_two {x : Perm (Fin 8)} (hx : x ^ 2 = 1)
    (hne : x ≠ 1) (hsign : Perm.sign x = 1) :
    x.cycleType = {2, 2} ∨ x.cycleType = {2, 2, 2, 2} := by
  have hrep := cycleType_eq_replicate_two_of_sq_eq_one hx
  have hk0 : Multiset.card x.cycleType ≠ 0 := fun h => hne (card_cycleType_eq_zero.1 h)
  have hsum : x.cycleType.sum ≤ 8 := by simpa using sum_cycleType_le x
  have hsgn := sign_of_cycleType x
  generalize Multiset.card x.cycleType = k at hrep hk0 hsum hsgn
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hsign, hrep, Multiset.sum_replicate, smul_eq_mul] at hsgn
  have hk4 : k ≤ 4 := by omega
  interval_cases k
  · exact absurd rfl hk0
  · exact absurd hsgn (by decide)
  · exact Or.inl hrep
  · exact absurd hsgn (by decide)
  · exact Or.inr hrep

private theorem ncard_cycleType_two_two :
    Set.ncard {x : Perm (Fin 8) | x.cycleType = {2, 2}} = 210 := by
  have h := Equiv.Perm.card_of_cycleType (Fin 8) {2, 2}
  have hset : {x : Perm (Fin 8) | x.cycleType = {2, 2}} =
      ↑({g | g.cycleType = {2, 2}} : Finset (Perm (Fin 8))) := by
    ext x
    simp
  rw [hset, Set.ncard_coe_finset, h]
  decide +kernel

theorem cycleType_eq_two_two_two_two_of_ncard_class_le {x : Perm (Fin 8)} (hx : x ^ 2 = 1)
    (hne : x ≠ 1) (hsign : Perm.sign x = 1)
    (hcard : Set.ncard {y : Perm (Fin 8) | y.cycleType = x.cycleType} ≤ 105) :
    x.cycleType = {2, 2, 2, 2} := by
  rcases cycleType_eq_two_two_or_two_two_two_two hx hne hsign with h | h
  · rw [h, ncard_cycleType_two_two] at hcard
    omega
  · exact h

end CFSG.ASVolI.ChH
