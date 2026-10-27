module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzCover

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo TauCeti CFSG.AGLEmbeddingD2
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def Seitz434OtherTwentySeven : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Subgroup.center X = ⊥ →
    IsSmallTwoOtherField (X ⧸ Subgroup.center X) →
    ∀ E : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤

namespace Res6Seitz

theorem not_isD2SeitzException_G2 (q : PrimePower) :
    ¬ IsD2SeitzException 3 (LieTypeIndex.G2 q) := by
  simp [IsD2SeitzException]

theorem not_isD2SeitzException_trialityD4 (q : PrimePower) :
    ¬ IsD2SeitzException 3 (LieTypeIndex.trialityD4 q) := by
  simp [IsD2SeitzException]

theorem not_isD2SeitzException_reeF4 (m : ℕ) :
    ¬ IsD2SeitzException 3 (LieTypeIndex.reeF4 m) := by
  simp [IsD2SeitzException]

end Res6Seitz

open Res6Seitz

end CFSG.RankThree.PartTwo.Sec4
