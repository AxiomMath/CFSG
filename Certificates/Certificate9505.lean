module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HNFiveData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.TcGen.F5Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.HNFive
  CFSG.Blueprint.NativeSporadic in
theorem certificate9505 : (tcCheck (opsP 5 133) HNSeed1 HNSeed2 CFSG.AGLEmbedding.R3.HNFive.tcNregs CFSG.AGLEmbedding.R3.HNFive.tcProg CFSG.AGLEmbedding.R3.HNFive.tcSpec = true)
    ∧ (cpCheck (opsP 5 133) HNSeed1 HNSeed2 CFSG.AGLEmbedding.R3.HNFive.cpNregs CFSG.AGLEmbedding.R3.HNFive.cpProg CFSG.AGLEmbedding.R3.HNFive.cpSpec = true)
    ∧ (CFSG.AGLEmbedding.R3.HNFive.cpSpec.noFun = true) := KernelTc.cert9505

end Certificates
