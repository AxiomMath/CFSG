module

public import CFSG.LocalAnalysis.StandardType.GGExcKGInndiagCIHolds
public import CFSG.LocalAnalysis.StandardType.GGExcKGToralFrameOfInput
public import CFSG.LocalAnalysis.StandardType.GGFinModelFamily
public import CFSG.LocalAnalysis.StandardType.GGLangAssembly
public import CFSG.LocalAnalysis.StandardType.GGLangDetectsTwoDispatch

public section

namespace CFSG.StandardType

theorem ggExcKGToralFrame_holds :
    GGExcKGToralFrame := by
  obtain ⟨Mod, hdata⟩ := GGFinModel.exists_ggModelFamily_langData
  exact ggExcKGToralFrame_of_input ggKGInndiagCI_holds
    (ggModelCompInput_of_langData (AlgebraicClosure (ZMod 2)) Mod hdata
      LangRat.langRatCentralizerDetectsP_holds)

end CFSG.StandardType

end
