module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Co1ThreeData
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.TcGen.F2Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Co1Three
  CFSG.Blueprint.NativeSporadic in
theorem certificate9503 : (tcCheck (ops2 24) Co1Seed1 Co1Seed2 CFSG.AGLEmbedding.R3.Co1Three.tcNregs CFSG.AGLEmbedding.R3.Co1Three.tcProg CFSG.AGLEmbedding.R3.Co1Three.tcSpec = true)
    ∧ (cpCheck (ops2 24) Co1Seed1 Co1Seed2 CFSG.AGLEmbedding.R3.Co1Three.cpNregs CFSG.AGLEmbedding.R3.Co1Three.cpProg CFSG.AGLEmbedding.R3.Co1Three.cpSpec = true)
    ∧ (CFSG.AGLEmbedding.R3.Co1Three.cpSpec.noFun = true) := KernelTc.cert9503

end Certificates
