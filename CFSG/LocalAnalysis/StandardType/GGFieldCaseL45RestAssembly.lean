module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigAssembly
public import CFSG.LocalAnalysis.StandardType.GGRecipeField

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRawPCyclicOn_notD4Three_of_split
    (hdone : GGRawPCyclicOn fun _ => GGRawPCyclicDoneLabel)
    (h : GGRawPCyclicOn fun p lab => GGNotD4Three p lab ∧ ¬ GGRawPCyclicDoneLabel lab) :
    GGRawPCyclicOn GGNotD4Three := fun p hp hp2 lab hlab hne => by
  by_cases hd : GGRawPCyclicDoneLabel lab
  · exact hdone p hp hp2 lab hlab hd
  · exact h p hp hp2 lab hlab ⟨hne, hd⟩

theorem ggL45MovingInput_of_rest_rankX
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoRestInput)
    (hcent : GGL45CentOutsideInput) (htorus : GGL45TorusInput) (hrankx : GGL45RankXInput)
    (hpc : GGRawPCyclicOn GGNotD4Three) (hD4 : GGL45CyclicD4Input) (hfive : GGL45FiveInput) :
    GGL45MovingInput :=
  ggL45MovingInput_of_rankX hraw (ggRawInndiagIsoInput_of_rest hiso)
    (ggL45CentInput_of_outside hcent) htorus hrankx hpc hD4 hfive

theorem ggL46CoreInput_of_rest_torus
    (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput) (hiso : GGRawInndiagIsoRestInput)
    (hcent : GGL45CentOutsideInput) (htorus : GGL45TorusInput) (hcyc : GGL46CyclicInput) :
    GGL46CoreInput :=
  ggL46CoreInput_of_torus hraw hcen (ggRawInndiagIsoInput_of_rest hiso)
    (ggL45CentInput_of_outside hcent) htorus hcyc

theorem ggL46Input_of_rest_torus
    (h43 : GGL43Input) (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hiso : GGRawInndiagIsoRestInput) (hcent : GGL45CentOutsideInput) (htorus : GGL45TorusInput)
    (hcyc : GGL46CyclicInput) : GGL46Input :=
  ggL46Input_of_torus h43 hraw hcen (ggRawInndiagIsoInput_of_rest hiso)
    (ggL45CentInput_of_outside hcent) htorus hcyc

theorem ggL45L46Inputs_of_rest_rankX
    (hN : GGInndiagNormalInput) (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hiso : GGRawInndiagIsoRestInput) (hcent : GGL45CentOutsideInput) (htorus : GGL45TorusInput)
    (hrankx : GGL45RankXInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hD4 : GGL45CyclicD4Input)
    (hfive : GGL45FiveInput) : GGL45Input ∧ GGL46CoreInput ∧ GGL46CyclicInput :=
  ⟨ggL45Input_of_moving_rawInnField hN hraw
      (ggL45MovingInput_of_rest_rankX hraw hiso hcent htorus hrankx hpc hD4 hfive),
    ggL46CoreInput_of_rest_torus hraw hcen hiso hcent htorus (ggL46CyclicInput_of_l45 hpc hD4),
    ggL46CyclicInput_of_l45 hpc hD4⟩

theorem ggL45L46Inputs_of_rest_pow
    (hN : GGInndiagNormalInput) (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hiso : GGRawInndiagIsoRestInput) (hcent : GGL45CentOutsideInput)
    (hab : GGL45TorusAbInput) (hpow : GGL45TorusPowInput) (hrankx : GGL45RankXInput)
    (hpc : GGRawPCyclicOn GGNotD4Three) (hD4 : GGL45CyclicD4Input) (hfive : GGL45FiveInput) :
    GGL45Input ∧ GGL46CoreInput ∧ GGL46CyclicInput :=
  ggL45L46Inputs_of_rest_rankX hN hraw hcen hiso hcent
    (ggL45TorusInput_of_pow hraw (ggRawInndiagIsoInput_of_rest hiso) hab hpow hrankx) hrankx hpc
    hD4 hfive

end CFSG.StandardType

end
