module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Label
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4E78
public import CFSG.LocalAnalysis.StandardType.GGAssemblyElevenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section F4

theorem ggExcNonsplitCoreInput_F4_holds : GGExcNonsplitCoreInput .F4 :=
  ggExcNonsplitCoreInput_F4_of_dvd ggF4NonsplitDvdInput_holds ggF4NonsplitCoprimeLabelInput_holds

end F4

section Round11Rest

theorem ggNonsplitCoreRound11_of_rest78 (hE6 : GGE6NonsplitCoreInput)
    (hE7 : GGE7NonsplitCoreRestInput) (hE8 : GGE8NonsplitCoreRestInput)
    (hTwE6 : GGNonsplitTag .twistedE6) : GGNonsplitCoreRound11 :=
  ⟨ggExcNonsplitCoreInput_F4_holds, hE6, ggExcNonsplitCoreInput_E7_of_rest hE7,
    ggExcNonsplitCoreInput_E8_of_rest hE8, hTwE6⟩

end Round11Rest

end CFSG.StandardType
