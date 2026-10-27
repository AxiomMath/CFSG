module

public import CFSG.Permutation.FiveTransitive.CyclePatternMixed

public section

namespace CFSG

namespace FiveTransitive.CyclePatternFinite

open Equiv CyclePatternRoots CyclePatternMixed

variable {X I J : Type*}

@[expose] def transport (e : I ≃ J) (π : Perm I) : Perm J := e.symm.trans (π.trans e)

@[expose] def patternEquiv (g : Perm X) (e : I ≃ J) (π : Perm I) :
    Pattern g π ≃ Pattern g (transport e π) where
  toFun a := ⟨e.symm.toEmbedding.trans a.val, by
    intro j
    simpa only [transport, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Equiv.trans_apply, Equiv.symm_apply_apply] using a.property (e.symm j)⟩
  invFun a := ⟨e.toEmbedding.trans a.val, by
    intro i
    simpa only [transport, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Equiv.trans_apply, Equiv.symm_apply_apply] using a.property (e i)⟩
  left_inv a := by
    apply Subtype.ext
    ext i
    exact congrArg a.val (e.symm_apply_apply i)
  right_inv a := by
    apply Subtype.ext
    ext j
    exact congrArg a.val (e.apply_symm_apply j)

@[expose] def doubleTwo : Perm (Fin 4) := transport finSumFinEquiv CyclePatternMixed.doubleTwo
@[expose] def fourTwo : Perm (Fin 6) := transport finSumFinEquiv CyclePatternMixed.fourTwo

@[expose] def eightPositions : (Fin 4 ⊕ (Fin 2 ⊕ Fin 2)) ≃ Fin 8 :=
  ((Equiv.refl (Fin 4)).sumCongr finSumFinEquiv).trans finSumFinEquiv

@[expose] def fourTwoTwo : Perm (Fin 8) := transport eightPositions CyclePatternMixed.fourTwoTwo

theorem card_double_two [Finite X] (g : Perm X) :
    Nat.card (Pattern g doubleTwo) = Nat.card (TwoRoot g) * (Nat.card (TwoRoot g) - 2) := by
  exact (Nat.card_congr (patternEquiv g finSumFinEquiv CyclePatternMixed.doubleTwo)).symm.trans
    (CyclePatternMixed.card_double_two g)

theorem card_four_two [Finite X] (g : Perm X) :
    Nat.card (Pattern g fourTwo) = Nat.card (FourRoot g) * Nat.card (TwoRoot g) := by
  exact (Nat.card_congr (patternEquiv g finSumFinEquiv CyclePatternMixed.fourTwo)).symm.trans
    (CyclePatternMixed.card_four_two g)

theorem card_four_two_two [Finite X] (g : Perm X) :
    Nat.card (Pattern g fourTwoTwo) =
      Nat.card (FourRoot g) * Nat.card (TwoRoot g) * (Nat.card (TwoRoot g) - 2) := by
  exact (Nat.card_congr (patternEquiv g eightPositions CyclePatternMixed.fourTwoTwo)).symm.trans
    (CyclePatternMixed.card_four_two_two g)

end FiveTransitive.CyclePatternFinite

end CFSG
