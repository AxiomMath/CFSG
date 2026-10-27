module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitVac
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitE6Two
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitHolds
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeWeylHolds

public section

namespace CFSG.StandardType

theorem ggNbrReflGenNonSplitInput_of_families
    (hF4R : GGF4ThreeNbrRankInput) (hPJ : GGStdSubPrimeInput) :
    GGNbrReflGenNonSplitInput :=
  ggNbrReflGenNonSplitInput_of_weyl
    (ggNbrTableBWeylNonSplitOn_of_families ggNbrTableBWeylNonSplitOn_vac
      ggNbrTableBWeylNonSplitOn_unitary ggNbrTableBWeylNonSplitOn_unitaryHyp
      ggNbrTableBWeylNonSplitOn_orth ggNbrTableBWeylNonSplitOn_sympLin
      ggNbrTableBWeylNonSplitOn_excPlus ggNbrTableBWeylNonSplitOn_e6Two
      ggNbrTableBWeylNonSplitOn_twE6)
    hF4R
    (ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds)
    hPJ ggUSixThreeNbrWeylInput_holds

end CFSG.StandardType

end
