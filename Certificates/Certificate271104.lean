module

public import Certificates.Data.Inputs2711eHN
import Certificates.Kernel.Gen2711.HNT
import CFSG.Certificates.Kernel.OpsLayMcertSoundP
import CFSG.Certificates.Kernel.GenWfSound

public section

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e
  CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e in
theorem certificate271104 : hnGenCheck = true := by
  have hl := HN.gen271104T_len
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨hm, -, -, h0, h1⟩ :=
    seedsLCP_sound (p := 5) (d := 133) (C := hnGenData.mcert) (S := fun i => HN.T.SL.getD i [])
      (k := 100) (kf := 8) (rA := 0) (rB := 1) HN.lay_ok rfl rfl HN.decA HN.decB HN.LA_eq
      HN.LB_eq HN.gen271104T_prog (by decide) (by decide) (eq_of_eqL HN.gen271104T_init) hl.1
      HN.gen271104T_ch hl.2 HN.gen271104T_fa HN.gen271104T_seeds
  have hD := HN.gen271104T_D
  simp only [Bool.and_eq_true] at hD
  obtain ⟨⟨hw, hm5⟩, hpc⟩ := hD
  rw [hnGenCheck, genCheck_of hm h0 h1 hw, hm5, hpc]
  rfl

end Certificates
