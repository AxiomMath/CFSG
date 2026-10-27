module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcFlatDefs
public import CFSG.LocalAnalysis.StandardType.GGFusionExceptionFull
public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlatMarking
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatRootCent
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummand
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcRows
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCountAll
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSchreier
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcOrthAll

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem ggRootCentAutKNotExcInput_of_flat (hN : GGRootCentAutKNotExcFlatInput)
    (h3 : GGRootCentAutKIIIFlatInput) (h4 : GGRootCentAutKIVFlatInput) :
    GGRootCentAutKNotExcInput :=
  ggRootCentAutKNotExcInput_of_flat_count ggRootInvolCountTag_holds
    (ggSchreierPerfectInput_of_lieSchreier
      (ggLieSchreierInput_of_schreierFor
        CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds)) hN h3 h4

end CFSG.StandardType
