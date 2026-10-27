module

public import Certificates.Data.Inputs2711eON
import Certificates.Kernel.Gen2711.ONT
import CFSG.Certificates.Kernel.OpsLayMcertSound
import CFSG.Certificates.Kernel.OpsLayTSound
import CFSG.Certificates.Kernel.GenWfSound

public section

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e
  CertificateChecks.KernelTc

namespace Certificates

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e in
theorem certificate271102 : onGenCheck = true := by
  have hK := ON.gen271102T_K
  rw [seedsLT_eq] at hK
  obtain ⟨hm, -, -, h0, h1⟩ :=
    seedsL_sound (d := 154) ON.lay_ok rfl rfl ON.decA ON.decB ON.LA_eq ON.LB_eq hK
  dsimp only at h0 h1
  rw [onGenCheck]
  exact genCheck_of hm h0 h1 ON.gen271102T_D

end Certificates
