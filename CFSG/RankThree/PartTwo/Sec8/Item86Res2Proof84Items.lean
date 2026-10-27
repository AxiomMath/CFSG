module

public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofChoice

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def Pair84GammaUL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → ∀ (b : G) (X : Subgroup G), b ∈ Subgroup.closure ({c, d} : Set G) →
      PairRel A c L b X → (∃ m : ℕ, IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m) →
      (∀ m : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) → IsGammaIndex A X c n

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
