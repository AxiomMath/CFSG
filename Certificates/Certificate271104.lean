module

public import Certificates.Data.Inputs2711eHN
import Certificates.Kernel.Gen2711.HNT
import CFSG.Certificates.Kernel.OpsLayMcertSoundP
import CFSG.Certificates.Kernel.OpsLayTSound
import CFSG.Certificates.Kernel.GenWfSound

public section

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e
  CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e in
theorem certificate271104 : hnGenCheck = true := by
  have hK := HN.gen271104T_K
  rw [seedsLT_eq] at hK
  obtain ⟨hm, -, -, h0, h1⟩ :=
    seedsLP_sound (p := 5) (d := 133) HN.lay_ok rfl rfl HN.decA HN.decB HN.LA_eq HN.LB_eq hK
  dsimp only at h0 h1
  have hD := HN.gen271104T_D
  simp only [Bool.and_eq_true] at hD
  obtain ⟨⟨hw, hm5⟩, hpc⟩ := hD
  rw [hnGenCheck, genCheck_of hm h0 h1 hw, hm5, hpc]
  rfl

end Certificates
