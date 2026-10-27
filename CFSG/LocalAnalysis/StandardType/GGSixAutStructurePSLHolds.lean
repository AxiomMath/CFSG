module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLRank
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLCoreCases
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4FactsTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem ggAutStructureAt_PSL : GGAutStructureAt .PSL :=
  AutPSL.ggAutStructureAt_PSL_of_inputs AutPSL.pslCoreInput_holds AutPSL.pslThreeRankInput_holds

theorem ggAutStructureInput_of_rest (h : GGAutStructureRest) : GGAutStructureInput :=
  ggAutStructureInput_of_psl_of_rest ggAutStructureAt_PSL h

end CFSG.StandardType
