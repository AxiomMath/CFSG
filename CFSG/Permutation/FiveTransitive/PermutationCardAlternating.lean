module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

namespace FiveTransitive.PermutationCardAlternating

theorem alternating_le_of_card
    (X : Type*) [Fintype X] [DecidableEq X] (P : Subgroup (Equiv.Perm X))
    (hn : 2 ≤ Fintype.card X)
    (hcard : Nat.card P = (Fintype.card X).factorial ∨
      Nat.card P = (Fintype.card X).factorial / 2) :
    alternatingGroup X ≤ P := by
  have hi := P.index_mul_card
  have hperm : Nat.card (Equiv.Perm X) = (Fintype.card X).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hperm] at hi
  apply Equiv.Perm.alternatingGroup_le_of_index_le_two
  rcases hcard with h | h
  · have he : P.index = 1 := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (Fintype.card X))
      simpa only [h, one_mul] using hi
    omega
  · have hd : 2 ∣ (Fintype.card X).factorial := by
      exact dvd_trans (by decide : 2 ∣ Nat.factorial 2) (Nat.factorial_dvd_factorial hn)
    have he : 2 * Nat.card P = (Fintype.card X).factorial := by
      rw [h]
      exact Nat.mul_div_cancel' hd
    have hp : 0 < Nat.card P := Nat.card_pos
    have heq : P.index = 2 := Nat.eq_of_mul_eq_mul_right hp (hi.trans he.symm)
    omega

end FiveTransitive.PermutationCardAlternating

end CFSG
