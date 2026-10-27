module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFAssembly
public import CFSG.LocalAnalysis.StandardType.GGExcKGToralFrameOfSF
public import CFSG.LocalAnalysis.StandardType.GGExcKGToralFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.AschbacherSeitz

section FullCerts

theorem ggExcKGToralFrame_of_input (hCI : GGKGInndiagCI) (h : GGModelCompInput) :
    GGExcKGToralFrame :=
  let ⟨Mod, hComp⟩ := h
  ggExcKGToralFrame_of_sfOutput (ggExcKGSFOutput_of_model hCI Mod hComp)

end FullCerts

end CFSG.StandardType
