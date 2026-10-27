module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionDataDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylInfDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionDefs

public section

namespace CFSG.StandardType

theorem ggSecFiveDataResAt_B_of_positions
    (hPos : BOriginalPositionInput) (hDX : GGSecFiveBCoordDExclInput) (hJ : BMaxJoinInput)
    (hRM : GGSecFiveReflMaxAt GGIsWeylMatrixB) (hBC : GGSecFiveBCoordBDataInput)
    (hLab : GGSecFiveBCoordBLabelInput) (hBP : GGSecFiveBPermDataInput) :
    GGSecFiveDataResAt (fun M => GGIsWeylMatrixB M) := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 ι M e hP hM
  have hRM' := hRM G p B Bs x L D J 𝒦 hR ι M e hP hM
  have hG0 := hJ G p B Bs x L D J 𝒦 hR ι M e hP hM hRM'
  obtain ⟨n, e', hn, rfl⟩ := hM
  have hP' := GGCoxeterPres.of_reindex_B hn hP
  obtain ⟨h4, eta, i0, hEta, hb | hd | ha⟩ := hPos G p B Bs x L D J 𝒦 hR n hn _ hP'
  · exact hBC G p B Bs x L D J 𝒦 hR hT1 n _ hP' h4 eta i0 hEta hb
      (hLab G p B Bs x L D J 𝒦 hR n h4 eta i0 hb) hRM' hG0
  · exact (hDX G p B Bs x L D J 𝒦 hR n eta i0 h4 hEta hd).elim
  · exact hBP G p B Bs x L D J 𝒦 hR hT1 n _ hP' h4 eta hEta ha hRM' hG0

end CFSG.StandardType

end
