module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def K_A5U34BorelQuotient : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), n = 2 →
    (IsL2Square X n ∨ IsL2U3Product X n) →
    IsPGroup 2 (Outer X) ∧
      ∀ S : Sylow 2 X,
        IsMulCommutative (TauCeti.Subgroup.normalizerQuotient (S : Subgroup X)) ∧
          ∃ E : Subgroup (TauCeti.Subgroup.normalizerQuotient (S : Subgroup X)),
            CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
