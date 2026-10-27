module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Co2ThreeData
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.TcGen.F2Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Co2Three
  CFSG.Blueprint.NativeSporadic in
theorem certificate9419 : (tcCheck (ops2 22) Co2Seed1 Co2Seed2 CFSG.AGLEmbedding.R3.Co2Three.tcNregs CFSG.AGLEmbedding.R3.Co2Three.tcProg CFSG.AGLEmbedding.R3.Co2Three.tcSpec = true)
    ∧ (cpCheck (ops2 22) Co2Seed1 Co2Seed2 CFSG.AGLEmbedding.R3.Co2Three.cpNregs CFSG.AGLEmbedding.R3.Co2Three.cpProg CFSG.AGLEmbedding.R3.Co2Three.cpSpec = true)
    ∧ (CFSG.AGLEmbedding.R3.Co2Three.cpSpec.noFun = true) := KernelTc.cert9419

end Certificates
