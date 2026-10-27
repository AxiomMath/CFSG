module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpPlacement
public import CFSG.LocalAnalysis.StandardType.GGQ2SpFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameAmbient
public import CFSG.LocalAnalysis.StandardType.GGQ2SpInnerDiagData
public import CFSG.LocalAnalysis.StandardType.GGQ2SpEleH
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIdem
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksGroup
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksQuasi
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksMark
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksComp
public import CFSG.LocalAnalysis.StandardType.GGQ2SpRealization
public import CFSG.LocalAnalysis.StandardType.GGQ2CoverComponents
public import CFSG.LocalAnalysis.StandardType.GGQ2AutomizerCover
public import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutAmb
public import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutZero
public import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutExt
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGQ2Frame.SpPlacement
  CFSG.StandardType.GGQ2Frame.SpBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem spComponentOccursIff_holds : SpComponentOccursIff :=
  spComponentOccursIff_of CoverComponents.isComponentOfCoverIff_holds
    (spIsComponentOfCentralizerTorusSetIff_of spExistsCodeOfIsPrimAdjIdemIn_holds
      spGlBlockCentralizerPlaneIdem_holds spNormalYcode_holds spYcodeLeCentralizer_holds
      spIsQuasisimpleYcode_holds spNotIsComponentOfYcode_holds)

theorem spComponentCentEq_holds : SpComponentCentEq :=
  spComponentCentEq_of CoverComponents.commuteCoverIff_holds spIsQuasisimpleYcode_holds
    spTauCommuteYcodeIff_holds

theorem spComponentInsideEq_holds : SpComponentInsideEq :=
  spComponentInsideEq_of CoverComponents.memDerivedComapIff_holds spIsQuasisimpleYcode_holds
    spTauMemYcodeIff_holds

theorem spComponentMarked_holds : SpComponentMarked :=
  spComponentMarked_of spIsQuasisimpleYcode_holds spMarkedYcode_holds

section


theorem placementCoreInputOn_sp_holds (ex : FrameKind → RawFrameData) :
    PlacementCoreInputOn (fun lab => lab.tag = .B ∨ lab.tag = .C)
      (catalogueOf classicalCatalogue ex) :=
  placementCoreInputOn_sp_of_pieces ggLabelRigidInput_holds ggG0_innerDiag_n_eq_one
    spInnerDiagData_holds exists_spFrame_holds spEleH_holds
    spComponentOccursIff_holds spComponentCentEq_holds spComponentInsideEq_holds
    spComponentMarked_holds ex

theorem placementInputOn_sp_holds (ex : FrameKind → RawFrameData) :
    PlacementInputOn (fun lab => lab.tag = .B ∨ lab.tag = .C)
      (catalogueOf classicalCatalogue ex) :=
  placementInputOn_sp_of_pieces ggLabelRigidInput_holds ggG0_innerDiag_n_eq_one
    spInnerDiagData_holds exists_spFrame_holds spEleH_holds
    spComponentOccursIff_holds spComponentCentEq_holds spComponentInsideEq_holds
    spComponentMarked_holds
    CoverComponents.automizerCoverEq_holds spAmbientTorusAut_holds
    (spComponentTorusAut_of_parts spZeroTorusAut_holds spExtTorusAut_holds)
    spIsQuasisimpleYcode_holds ex

end

end CFSG.StandardType.GGQ2Frame

end
