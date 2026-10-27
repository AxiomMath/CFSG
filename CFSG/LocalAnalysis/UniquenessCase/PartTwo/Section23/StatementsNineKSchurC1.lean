module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def KSchurC1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal],
    ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ →
      Z ≤ Subgroup.center X → Odd (Nat.card ↥Z) →
      ((∃ n : ℕ, 3 ≤ n ∧ IsSp4 (X ⧸ Z) n) ∨
        (∃ a : ℕ, 2 ≤ a ∧ IsSUn (X ⧸ Z) 4 a) ∨
        (∃ n : ℕ, 3 ≤ n ∧ IsOmegaMinus (X ⧸ Z) 6 n)) →
      Z = ⊥

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
