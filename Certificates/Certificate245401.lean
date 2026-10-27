module

public import Certificates.Data.Inputs245dU43
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenU43Data
public import Certificates.Data.CFSGNative.SectionRank.F3
import Certificates.Kernel.TcGen.U43In245d
import Certificates.Kernel.TcGen.F3Glue

public section

namespace Certificates

open CFSG.AGLEmbedding.R3 CertificateChecks.KernelTc

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.LocalAnalysis.GLTheoremB.MovingAround in
theorem certificate245401 : (cpCheck (ops3 8) U43Three.seedA U43Three.seedB Inputs245d.nregs Inputs245d.cpProg
      Inputs245d.cpSpec = true) ∧ (Inputs245d.cpSpec.noFun = true) :=
  ⟨cp3_of U43.lay_ok rfl rfl U43.decA U43.decB U43.LA_eq U43.LB_eq (by decide +kernel)
    In245d.cp_K, by decide +kernel⟩

end Certificates
