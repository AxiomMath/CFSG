module

public import Certificates.Data.Inputs2711eCo1
import Certificates.Kernel.Gen2711.Co1T
import Certificates.Kernel.TcGen.F2Glue
import CFSG.Certificates.Kernel.OpsMcertTSound
import CFSG.Certificates.Kernel.GenWfSound

public section

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e CertificateChecks.KernelTc

namespace Certificates

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e in
theorem certificate271103 : co1GenCheck = true := by
  have hrA : 0 < co1GenData.nregs := by decide
  have hrB : 1 < co1GenData.nregs := by decide
  have hK := gen271103T_K
  rw [CFSG.KC.OpsMT.seedsT_eq] at hK
  obtain ⟨hm, h0, h1⟩ := seeds_of_N (hom2 24 (by norm_num)) c1A c1B trivial trivial
    (fs := co1GenData.facts) hrA hrB hK
  have hD := gen271103T_D
  simp only [Bool.and_eq_true] at hD
  obtain ⟨⟨hw, hpc⟩, hind⟩ := hD
  rw [co1GenCheck, genCheck_of hm h0 h1 hw, hpc, hind]
  rfl

end Certificates
