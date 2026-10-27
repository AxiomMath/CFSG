module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsSU
public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsTwE6

public section

namespace CFSG.StandardType

theorem ggSixFieldFiveInput_of_omega_e8_twE6 (hPlus : GGFieldFiveNbrTag .POmegaPlus)
    (hMinus : GGFieldFiveNbrTag .POmegaMinus) (hE8 : GGFieldFiveNbrTag .E8)
    (hTwE6 : GGFieldFiveRankTag .twistedE6) : GGSixFieldFiveInput :=
  ggSixFieldFiveInput_of_rest ggFieldFiveNbrTag_PSU hPlus hMinus hE8 ggFieldFiveRankTag_F4
    ggFieldFiveRankTag_E6 ggFieldFiveRankTag_E7 hTwE6

theorem ggSixFieldFiveInput_of_omega_e8 (hPlus : GGFieldFiveNbrTag .POmegaPlus)
    (hMinus : GGFieldFiveNbrTag .POmegaMinus) (hE8 : GGFieldFiveNbrTag .E8) :
    GGSixFieldFiveInput :=
  ggSixFieldFiveInput_of_omega_e8_twE6 hPlus hMinus hE8 ggFieldFiveRankTag_twistedE6

end CFSG.StandardType
