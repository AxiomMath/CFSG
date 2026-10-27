module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Blueprint (LieModel)

@[expose] def K_ThreeCentralRankTwo : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : CFSG.Open.StatedLieTag) (m f : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 f → LieModel (K ⧸ Subgroup.center K) t m 2 f →
    CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
    3 ∣ Nat.card (Subgroup.center K) → CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 →
      (t = .PSL ∧ m = 3 ∧ Even f ∧ Nat.card (Subgroup.center K) = 3 ∧
          2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)) ∨
        (t = .PSU ∧ m = 3 ∧ Odd f)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
