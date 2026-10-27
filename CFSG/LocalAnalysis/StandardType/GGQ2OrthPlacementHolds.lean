module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthPlacement
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocks
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthRealization
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthInnerDiagData
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthEleH
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthSmallRank
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthTorusAut
public import CFSG.LocalAnalysis.StandardType.GGQ2AutomizerCover
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameAmbient
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGQ2OrthFrameExists
import CFSG.LocalAnalysis.StandardType.GGQ2OrthTorusAutHolds

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGQ2Frame.OrthPlacement
  CFSG.StandardType.GGQ2Frame.OrthBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem orth_hOcc : OrthComponentOccursIff :=
  orthComponentOccursIff_of orthIsComponentOfCentralizerTorusSetIff_holds

private theorem orth_hCent : OrthComponentCentEq :=
  orthComponentCentEq_of orthIsQuasisimpleYcode_holds orthTauCommuteYcodeIff_holds

private theorem orth_hIn : OrthComponentInsideEq :=
  orthComponentInsideEq_of orthIsQuasisimpleYcode_holds orthTauMemYcodeIff_holds

private theorem orth_hMk : OrthComponentMarked :=
  orthComponentMarked_of orthIsQuasisimpleYcode_holds orthMarkedYcode_holds

section


theorem placementCoreInputOn_orth_of_frame (hF : ExistsOrthFrame)
    (ex : FrameKind → RawFrameData) :
    PlacementCoreInputOn (fun lab => lab.tag = .D ∨ lab.tag = .twD)
      (catalogueOf classicalCatalogue ex) :=
  placementCoreInputOn_orth_of_pieces ggLabelRigidInput_holds ggG0_innerDiag_n_eq_one
    orthInnerDiagData_holds hF orthEleH_holds orthSmallRankVacuous_holds orth_hOcc orth_hCent
    orth_hIn orth_hMk ex

theorem placementInputOn_orth_of_frame (hF : ExistsOrthFrame) (hComp : OrthComponentTorusAut)
    (ex : FrameKind → RawFrameData) :
    PlacementInputOn (fun lab => lab.tag = .D ∨ lab.tag = .twD)
      (catalogueOf classicalCatalogue ex) :=
  placementInputOn_orth_of_pieces ggLabelRigidInput_holds ggG0_innerDiag_n_eq_one
    orthInnerDiagData_holds hF orthEleH_holds orthSmallRankVacuous_holds orth_hOcc orth_hCent
    orth_hIn orth_hMk CoverComponents.automizerCoverEq_holds orthAmbientTorusAut_holds hComp
    orthIsQuasisimpleYcode_holds ex

theorem placementCoreInputOn_orth_holds (ex : FrameKind → RawFrameData) :
    PlacementCoreInputOn (fun lab => lab.tag = .D ∨ lab.tag = .twD)
      (catalogueOf classicalCatalogue ex) :=
  placementCoreInputOn_orth_of_frame existsOrthFrame_holds ex

theorem placementInputOn_orth_holds (ex : FrameKind → RawFrameData) :
    PlacementInputOn (fun lab => lab.tag = .D ∨ lab.tag = .twD)
      (catalogueOf classicalCatalogue ex) :=
  placementInputOn_orth_of_frame existsOrthFrame_holds orthComponentTorusAut_holds ex

end

end CFSG.StandardType.GGQ2Frame
