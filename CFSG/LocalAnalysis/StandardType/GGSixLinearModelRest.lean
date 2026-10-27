module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestField
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestTriple
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestSURank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

theorem ggSixLinearTorusModelV2On_PSL : GGSixLinearTorusModelV2On .PSL :=
  ggSixLinearTorusModelV2On_PSL_of_inputs ggSixLinearFieldOrderPInput_holds
    ggLinearRegularConjInput_holds ggLinearTypeAkTripleInput_holds

theorem ggSixLinearTorusModelV2Input_of_psu (hU : GGSixLinearTorusModelV2On .PSU) :
    GGSixLinearTorusModelV2Input :=
  ggSixLinearTorusModelV2Input_of_tags ggSixLinearTorusModelV2On_PSL hU

theorem ggSixLSixTwelveInput_of_psu_torus (hTU : GGSixLinearTorusModelV2On .PSU) :
    GGSixLSixTwelveInput :=
  ggSixLSixTwelveInput_of_kg_v2 ggSixLinearRankInput_holds (ggSixLinearTorusModelV2Input_of_psu hTU)

end Inputs

end CFSG.StandardType
