module

public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatKGDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ExcAdjHolds
public import CFSG.LocalAnalysis.StandardType.GGE0ExcE6Holds
public import CFSG.LocalAnalysis.StandardType.GGE0PSL
public import CFSG.LocalAnalysis.StandardType.GGE0PSU
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagClassical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem ggE0Rest_holds
    
    : GGE0Rest :=
  ⟨ggE0At_PSL, ggE0At_PSU, ggE0At_PSp, ggE0At_POmegaPlus, ggE0At_POmegaMinus, ggE0At_F4_holds,
    ggE0At_E6_holds, ggE0At_E7_holds, ggE0At_E8_holds, ggE0At_twistedE6_holds⟩

theorem ggE0InnerDiagInput_holds
    
    : GGE0InnerDiagInput :=
  ggE0InnerDiagInput_of_rest ggE0Rest_holds

end CFSG.StandardType
