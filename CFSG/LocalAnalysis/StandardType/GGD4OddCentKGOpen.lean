module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKGOpenDefs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKGRest
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldReduce
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldCent

public section

namespace CFSG.StandardType

theorem ggD4OddCentKGInputsRest_of_open (h : GGD4OddCentKGInputsOpen) :
    GGD4OddCentKGInputsRest := by
  obtain ⟨h1, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, ggD4OddCentFieldInput_of_kg5 ggD4FieldCentralizerInput_holds, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end CFSG.StandardType
