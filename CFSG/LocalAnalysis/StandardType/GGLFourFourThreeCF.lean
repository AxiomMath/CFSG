module

public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeCFNotInner
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeCFMcL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL44iiiMarkingInput_of_tableB (hBN : GGBstarNbrNormalInput) (hgr : GGNbrGraphInput)
    (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput) (hlang : GGRawFieldConjInput)
    (hL : GGLBalanceInput) (hJp : GGStdSubPrimeInput) (hI2 : GGStdSubBstarMeetInput)
    (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput) (hTBM : GGTableBModuleInput)
    (hTBA : GGTableBActionInput) (hTBK : GGTableBNbrInnerInput) (hlax : GGNbrLangAxisInput) :
    GGL44iiiMarkingInput :=
  ggL44iiiMarkingInput_of_parts hBN hgr hraw hcen hlang hL hJp hI2
    (ggL44iiiNotInnerInput_of_tableB hL hJp hI2 hTBK)
    (ggL44iiiMcLaughlinInput_of_lang hTB hNN hTBM hTBA hlax)

theorem ggL44iiiMarkingInput_of_tableB_torus (hBN : GGBstarNbrNormalInput)
    (hgr : GGNbrGraphInput) (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hlang : GGRawFieldConjInput) (hL : GGLBalanceInput) (hJp : GGStdSubPrimeInput)
    (hI2 : GGStdSubBstarMeetInput) (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (hTBK : GGTableBNbrInnerInput)
    (hlt : GGNbrLangTorusAxisInput) : GGL44iiiMarkingInput :=
  ggL44iiiMarkingInput_of_tableB hBN hgr hraw hcen hlang hL hJp hI2 hTB hNN hTBM hTBA hTBK
    (ggNbrLangAxisInput_of_torus hlt)

end CFSG.StandardType

end
