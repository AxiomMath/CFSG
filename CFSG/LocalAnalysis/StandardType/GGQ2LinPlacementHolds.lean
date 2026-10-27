module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinPlacement
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameAmbient
import CFSG.LocalAnalysis.StandardType.GGQ2LinInnerDiagData
import CFSG.LocalAnalysis.StandardType.GGQ2LinA1FourVacuous
import CFSG.LocalAnalysis.StandardType.GGQ2LinFrame
import CFSG.LocalAnalysis.StandardType.GGQ2LinFrameCard
import CFSG.LocalAnalysis.StandardType.GGQ2LinEleH
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksIdem
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksGroup
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksComp
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksMark
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksCent
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksCentExt
import CFSG.LocalAnalysis.StandardType.GGQ2LinRealization
import CFSG.LocalAnalysis.StandardType.GGQ2LinTorusAutAmb
import CFSG.LocalAnalysis.StandardType.GGQ2LinTorusAutZero
import CFSG.LocalAnalysis.StandardType.GGQ2LinTorusAutYcode
import CFSG.LocalAnalysis.StandardType.GGQ2CoverComponents
import CFSG.LocalAnalysis.StandardType.GGQ2AutomizerCover

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGQ2Frame.LinPlacement
  CFSG.StandardType.GGQ2Frame.LinBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace LinBlocks

theorem linZeroTorusAut_holds : LinZeroTorusAut := by
  intro K _ _ _ ζ t ε hK hζ S hS
  rw [ycode_zero_eq_blockGroup hK hS,
    torusAut_blockGroup_zero_eq linTorusAutSubsetSignedPerm_holds hK hζ S]
  rfl

theorem linExtTorusAut_holds : LinExtTorusAut := by
  intro K _ _ _ ζ t ε hK hζ e he
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (PlaneRaw.Code.extSupport e).card by omega)
  have hei : e i ≠ 0 := (PlaneRaw.mem_extSupport e i).mp hi
  have hz : tau ζ t ε (Pi.single i 1) ∉ Ycode ζ t ε (PlaneRaw.Code.extension e) := by
    rw [tau_mem_ycode_extension_iff hK hζ he, PlaneRaw.mem_insideExt]
    rintro ⟨-, hsum⟩
    exact hei (by simpa [Pi.single_apply] using hsum)
  exact torusAut_ycode_extension_eq linTorusAutSubsetSignedPerm_holds hK hζ
    (relIndex_ycode_extension hK hζ he) hei hz

theorem linComponentTorusAut_holds : LinComponentTorusAut :=
  linComponentTorusAut_of_parts linZeroTorusAut_holds linExtTorusAut_holds

theorem linTauMemYcodeIff_holds : LinTauMemYcodeIff := by
  intro K _ _ _ ζ t ε hK hζ c hc u
  cases c with
  | zero S => exact tau_mem_ycode_zero_iff hK hζ hc u
  | extension e => exact tau_mem_ycode_extension_iff hK hζ hc.2 u

theorem linTauCommuteYcodeIff_holds : LinTauCommuteYcodeIff := by
  intro K _ _ _ ζ t ε hK hζ c hc u
  cases c with
  | zero S => exact tau_commute_ycode_zero_iff hK hζ hc u
  | extension e =>
    exact tau_commute_ycode_extension_iff_of_relIndex hK hζ hc.2
      (relIndex_ycode_extension hK hζ hc.2) u

end LinBlocks

namespace LinPlacement

theorem linComponentCentEq_holds : LinComponentCentEq :=
  linComponentCentEq_of CoverComponents.commuteCoverIff_holds linIsQuasisimpleYcode_holds
    linTauCommuteYcodeIff_holds

theorem linComponentInsideEq_holds : LinComponentInsideEq :=
  linComponentInsideEq_of CoverComponents.memDerivedComapIff_holds linIsQuasisimpleYcode_holds
    linTauMemYcodeIff_holds

theorem linComponentMarked_holds : LinComponentMarked :=
  linComponentMarked_of linIsQuasisimpleYcode_holds linMarkedYcode_holds


theorem linComponentOccursIff_holds : LinComponentOccursIff :=
  linComponentOccursIff_of CoverComponents.isComponentOfCoverIff_holds
    (linIsComponentOfCentralizerTorusSetIff_of linExistsCodeOfIsPrimIdemIn_holds
      (linGlBlockCentralizerKeyIdem_of linIsPrimIdemInKeyIdem_holds)
      (linNormalYcode_of linIsPrimIdemInKeyIdem_holds) linYcodeLeCentralizer_holds
      linIsQuasisimpleYcode_holds linNotIsComponentOfYcode_holds)

end LinPlacement

section


theorem placementCoreInputOn_lin_holds (ex : FrameKind → RawFrameData) :
    PlacementCoreInputOn (fun lab => lab.tag = .A) (catalogueOf classicalCatalogue ex) :=
  placementCoreInputOn_lin_of_pieces ggLabelRigidInput_holds ggG0_innerDiag_n_eq_one
    linInnerDiagData_holds linA1FourVacuous_holds (existsLinFrame_of_cardEEq linCardEEq_holds)
    linEleH_holds linComponentOccursIff_holds linComponentCentEq_holds linComponentInsideEq_holds
    linComponentMarked_holds ex

theorem placementInputOn_lin_holds (ex : FrameKind → RawFrameData) :
    PlacementInputOn (fun lab => lab.tag = .A) (catalogueOf classicalCatalogue ex) :=
  placementInputOn_lin_of_pieces ggLabelRigidInput_holds ggG0_innerDiag_n_eq_one
    linInnerDiagData_holds linA1FourVacuous_holds (existsLinFrame_of_cardEEq linCardEEq_holds)
    linEleH_holds linComponentOccursIff_holds linComponentCentEq_holds linComponentInsideEq_holds
    linComponentMarked_holds CoverComponents.automizerCoverEq_holds linAmbientTorusAut_holds
    linComponentTorusAut_holds linIsQuasisimpleYcode_holds ex

end

end CFSG.StandardType.GGQ2Frame
