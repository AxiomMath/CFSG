module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def K_BorelOvergroup : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 3 ≤ n →
    (IsSp4 X n ∨ IsL2Square X n ∨ S17.IsL2U3Product X n ∨ IsSzSquare X n) →
    ∀ (U : Sylow 2 X) (Y : Subgroup X), (U : Subgroup X) ≤ Y →
      Nat.card Y ∣ Nat.card U * (2 ^ n - 1) ^ 2 →
        Y ≤ normalizer ((U : Subgroup X) : Set X)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
