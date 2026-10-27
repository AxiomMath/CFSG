module

public import CFSG.Permutation.FiveTransitive.CyclePatternFinite
public import Mathlib.SetTheory.Cardinal.NatCard

public section

namespace CFSG

namespace FiveTransitive.TwoRootDoubleSwap

open Equiv CyclePatternRoots

theorem exists_double_two_pattern {X : Type*} [Finite X] (g : Perm X)
    (h : 4 ≤ Nat.card (TwoRoot g)) : Nonempty (Pattern g CyclePatternFinite.doubleTwo) := by
  apply Finite.card_pos_iff.mp
  rw [CyclePatternFinite.card_double_two]
  exact Nat.mul_pos (by omega) (by omega)

end FiveTransitive.TwoRootDoubleSwap

end CFSG
