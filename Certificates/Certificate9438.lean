module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenO73Data
public import Certificates.Data.CFSGNative.SectionRank.F3
import Certificates.Kernel.TcGen.Small3
import Certificates.Kernel.TcGen.F3Glue

public section

namespace Certificates

open CFSG.AGLEmbedding.R3 CertificateChecks.KernelTc

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 in
theorem certificate9438 : (cpCheck (ops3 7) O73Three.seedA O73Three.seedB O73Three.nregs O73Three.cpProg
      O73Three.cpSpec = true) ∧ (O73Three.cpSpec.noFun = true) :=
  ⟨cp3_of O73.lay_ok rfl rfl O73.decA O73.decB O73.LA_eq O73.LB_eq (by decide +kernel) O73.cp_K,
    by decide +kernel⟩

end Certificates
