module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.RankThree.PartTwo.Sec11.Item11CloseChain

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

theorem coverInputs46_closed
    : Sec4.Census.CoverInputs46 :=
  Sec4.Census.CoverInputs46.of_open Sec4.Census.coverSLThree46
    (Sec4.Census.coverCenterThree_of_rest
      (Sec4.Census.coverCenterThreeRest_of Sec11.Close.closed_tBLitGriessMultipliersAllModels))
    Sec4.Census.nineCoverU43RankFour

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
