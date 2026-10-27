module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut

public section

namespace CFSG.StandardType

theorem ggFieldNbrSplitInput_of_tableB (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) : GGFieldNbrSplitInput :=
  fun _ _ _ _ _ _ _ _ _ _ hcfg => ggFieldNbrSplit_of_tableB hTB hNN hTBM hTBA hcfg

theorem ggFieldNbrFieldAutInput_of_noBL5 (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (hmk : GGL44iiiMarkingInput)
    (hraw : GGRawInnFieldInput) : GGFieldNbrFieldAutInput :=
  fun _ _ _ _ _ _ _ _ _ _ hcfg => ggFieldNbrFieldAut_of_inputs hTB hNN hTBM hTBA hmk hraw hcfg

theorem ggFieldNbrInnerInput_of_noBL5 (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (hmk : GGL44iiiMarkingInput)
    (hraw : GGRawInnFieldInput) : GGFieldNbrInnerInput :=
  ggFieldNbrInnerInput_of_split (ggFieldNbrSplitInput_of_tableB hTB hNN hTBM hTBA)
    (ggFieldNbrFieldAutInput_of_noBL5 hTB hNN hTBM hTBA hmk hraw)

end CFSG.StandardType

end
