module

public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeRepair
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL44iiiMarkingInput_of_tableB_exc (hBN : GGBstarNbrNormalInput) (hgr : GGNbrGraphInput)
    (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hlang : GGRawFieldConjInputExc) (hL : GGLBalanceInput) (hJp : GGStdSubPrimeInput)
    (hI2 : GGStdSubBstarMeetInput) (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (hTBK : GGTableBNbrInnerInput)
    (hlax : GGNbrLangAxisInput) (hD4 : GGL44iiiTriD4LangInput) : GGL44iiiMarkingInput :=
  ggL44iiiMarkingInput_of_parts_exc hBN hgr hraw hcen hlang hL hJp hI2
    (ggL44iiiNotInnerInput_of_tableB hL hJp hI2 hTBK)
    (ggL44iiiMcLaughlinInput_of_lang hTB hNN hTBM hTBA hlax) hD4

end CFSG.StandardType

end
