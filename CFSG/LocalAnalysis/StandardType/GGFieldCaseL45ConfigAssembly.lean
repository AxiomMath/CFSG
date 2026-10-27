module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigCover
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigCent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45MovingInput_of_rest
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoRestInput)
    (hcent : GGL45CentOutsideInput) (homega : GGL45OmegaInput) (hrank : GGL45RankInput)
    (hfive : GGL45FiveInput) : GGL45MovingInput :=
  ggL45MovingInput_of_inputs hraw (ggRawInndiagIsoInput_of_rest hiso)
    (ggL45CentInput_of_outside hcent) homega hrank hfive

theorem ggL45Input_of_rest
    (hN : GGInndiagNormalInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoRestInput)
    (hcent : GGL45CentOutsideInput) (homega : GGL45OmegaInput) (hrank : GGL45RankInput)
    (hfive : GGL45FiveInput) : GGL45Input :=
  ggL45Input_of_inputs hN hraw (ggRawInndiagIsoInput_of_rest hiso)
    (ggL45CentInput_of_outside hcent) homega hrank hfive

theorem ggL46CoreInput_of_rest
    (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput) (hiso : GGRawInndiagIsoRestInput)
    (hcent : GGL45CentOutsideInput) (homega : GGL45OmegaInput) (htorus : GGL45TorusInput)
    (hcyc : GGL46CyclicInput) : GGL46CoreInput :=
  ggL46CoreInput_of_cyclic hraw hcen (ggRawInndiagIsoInput_of_rest hiso)
    (ggL45CentInput_of_outside hcent) homega htorus hcyc

theorem ggL46Input_of_rest
    (h43 : GGL43Input) (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hiso : GGRawInndiagIsoRestInput) (hcent : GGL45CentOutsideInput) (homega : GGL45OmegaInput)
    (htorus : GGL45TorusInput) (hcyc : GGL46CyclicInput) : GGL46Input :=
  ggL46Input_of_cyclic h43 hraw hcen (ggRawInndiagIsoInput_of_rest hiso)
    (ggL45CentInput_of_outside hcent) homega htorus hcyc

end CFSG.StandardType

end
