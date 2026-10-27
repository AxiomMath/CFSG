module

public import CFSG.LocalAnalysis.StandardType.GGTBJLabelSides
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyStages
public import CFSG.LocalAnalysis.StandardType.GGResSevenNbr
public import CFSG.LocalAnalysis.StandardType.GGResTrialityNbr
public import CFSG.LocalAnalysis.StandardType.GGTCJD4Tag

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJLeftOn_seven (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) :
    GGTBJLeftOn ggTBJSevenLabel := by
  intro G _ _ p B Bs x L D J y K hH _ hL _
  exfalso
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hT, -⟩ := largeEvenMarking_exists_hasLabel hL
  exact ggSeven_L_absurd hTCJ hRig hH.1 hT.1 hH.2.2.2.2.1 hlab hhas hT.2

theorem ggTBJNbrOn_seven (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) :
    GGTBJNbrOn ggTBJSevenLabel := by
  intro G _ _ p B Bs x L D J y K hH _ hK _
  exfalso
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hT, -⟩ := largeEvenMarking_exists_hasLabel hK
  exact ggSeven_K_absurd hTCJ hRig hTPn hA8 hraw hiso hH hT.1 hlab hhas hT.2

theorem ggTBJOrderRestSplitAUnitRankThree_of_restUnitSeven (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (h : GGTBJOrderRestSplitAUnitSevenInput) : GGTBJOrderRestSplitAUnitRankThreeInput :=
  GGTBJOrdinaryOutside.of_proved (ggTBJLeftOn_seven hTCJ hRig)
    (ggTBJNbrOn_seven hTCJ hRig hTPn hA8 hraw hiso) h

end CFSG.StandardType

end
