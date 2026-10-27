module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARank
public import CFSG.LocalAnalysis.StandardType.GGResHdRoNarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLargeRowKDatum_of_inputs (hT : GGTBTorANarrow) (hLift : GGTBTorLiftADepRows)
    (hRig : GGLabelRigidInput) : GGLargeRowKDatum := by
  intro G _ _ p _ B Bs x L D J y K N hH hrow
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hRow⟩ := hrow
  obtain ⟨hRow2, hrankX, hN⟩ := hRow
  obtain ⟨htagX, hdvdX, hdvdMX⟩ := l05nAK_row_facts hRow2 hrankX
  have hIlab := l05nAK_innerDiagOnLabel hRig hH hXΛ hXlab htagX hrankX hdvdX hdvdMX
  obtain ⟨lab, hlabΛ, hlabHas, hlabTag, hlabRank, hlabDvd, hlabDvdM, hDatumLab⟩ :=
    ggResXDatumA_of_tbTorA_rank_K hT hLift hH hIlab
  have hiso2 : GGLabelIso lab labX :=
    hRig lab labX (↥K ⧸ Subgroup.center ↥K) hlabΛ hXΛ hlabHas hXlab
  have hEq2 : lab = labX := l05nAK_iso_eq hiso2 hlabTag (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · rw [← hN]; exact hdvdX
  · have hEq3 : N - 1 = labX.rank := by omega
    rw [hEq3]
    exact hEq2 ▸ hDatumLab

end CFSG.StandardType

end
