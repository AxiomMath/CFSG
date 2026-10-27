module

public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

@[expose] def K11 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X →
    (∀ P : Subgroup X, IsPGroup 3 P → IsCyclic P) →
    ((∃ p f : ℕ, CFSG.Blueprint.LieModel X .PSL 2 p f) ∨
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor X .J1) →
    ∀ A W : Subgroup X, Nat.card A = 3 → Subgroup.normalizer (A : Set X) ≤ W →
      ¬ CFSG.HallHigman.IsPSolvable 3 W → W = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
