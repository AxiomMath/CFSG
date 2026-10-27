module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplit
public import CFSG.LocalAnalysis.StandardType.GGInndiagThreeRankTwoLabels

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.StandardType.SCFourCover

@[expose] def SVRank (F : LargeEvenLieTag → Prop) : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → F lab.tag →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagThreeRankTwo)

end CFSG.StandardType.TablePThreeKG

end
