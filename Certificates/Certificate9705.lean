module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenU43Data
public import Certificates.Data.CFSGNative.SectionRank.F3
import Certificates.Kernel.TcGen.Small3
import Certificates.Kernel.TcGen.F3Glue

public section

namespace Certificates

open CFSG.AGLEmbedding.R3 CertificateChecks.KernelTc

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 in
theorem certificate9705 : (cpCheck (ops3 8) U43Three.seedA U43Three.seedB U43Three.nregs U43Three.cpProg
      U43Three.cpSpec = true) ∧ (U43Three.cpSpec.noFun = true) :=
  ⟨cp3_of U43.lay_ok rfl rfl U43.decA U43.decB U43.LA_eq U43.LB_eq (by decide +kernel) U43.cp_K,
    by decide +kernel⟩

end Certificates
