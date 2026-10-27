module

public import CFSG.Permutation.FiveTransitive.SixPointCycleCounts
public import CFSG.Permutation.FiveTransitive.EvenSixOrderFourFixed

public section

namespace CFSG

namespace FiveTransitive.SixPointDoubleSwapShape

open Equiv CyclePatternRoots

theorem square_one_and_fixed_two
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (g : Perm X) (hsign : g.sign = 1) (hg4 : g ^ 4 = 1)
    (htwo : 4 ≤ Nat.card (TwoRoot g)) :
    g ^ 2 = 1 ∧ Nat.card (Function.fixedPoints g) = 2 := by
  have hfix := (SixPointCycleCounts.counts hX g hsign).2 htwo
  have hg2 : g ^ 2 = 1 := by
    by_contra hn
    have hz := (EvenSixOrderFourFixed.fixed_card_zero_and_square_two X hX g hsign hg4 hn).1
    omega
  have hne : g ≠ 1 := by
    intro h
    obtain ⟨x⟩ := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card (TwoRoot g))).1
    exact x.property.2 (congrArg (fun p : Perm X => p x.val) h)
  exact ⟨hg2, EvenSixInvolution.fixed_card_eq_two_of_ne_one hX g hg2 hsign hne⟩

end FiveTransitive.SixPointDoubleSwapShape

end CFSG
