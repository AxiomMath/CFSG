module

public import CFSG.Permutation.FiveTransitive.EvenSixInvolution
public import CFSG.Permutation.FiveTransitive.SixPointEvenOrderFour
public import CFSG.Permutation.FiveTransitive.TwoElementFixedBound

public section

namespace CFSG

namespace FiveTransitive.EvenSixOrderFourFixed

open Equiv CyclePatternRoots

theorem fixed_card_zero_and_square_two
    (X : Type*) [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (g : Perm X) (hsign : g.sign = 1) (hg4 : g ^ 4 = 1) (hg2 : g ^ 2 ≠ 1) :
    Nat.card (Function.fixedPoints g) = 0 ∧
      Nat.card (Function.fixedPoints (g ^ 2 : Perm X)) = 2 := by
  have hsquare : (g ^ 2 : Perm X) ^ 2 = 1 := by rw [← pow_mul]; exact hg4
  have hsign2 : (g ^ 2 : Perm X).sign = 1 := by rw [map_pow, hsign, one_pow]
  have hfix2 := EvenSixInvolution.fixed_card_eq_two_of_ne_one hX (g ^ 2) hsquare hsign2 hg2
  obtain ⟨x, hx2, hx⟩ := SixPointEvenOrderFour.exists_fixed_square_not_fixed X hX g hsign hg4 hg2
  have hpos : 0 < Nat.card (TwoRoot g) := by
    apply Nat.card_pos_iff.mpr
    exact ⟨⟨⟨x, hx2, hx⟩⟩, inferInstance⟩
  have heven := Nat.even_iff.mp (TwoRootEven.even_two_card g)
  have hsum := TwoElementFixedBound.fixed_square_card g
  rw [hfix2] at hsum
  exact ⟨by omega, hfix2⟩

end FiveTransitive.EvenSixOrderFourFixed

end CFSG
