module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Co3ThreeData
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.TcGen.F2Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Co3Three
  CFSG.Blueprint.NativeSporadic in
theorem certificate9418 : (tcCheck (ops2 22) Co3Seed1 Co3Seed2 CFSG.AGLEmbedding.R3.Co3Three.tcNregs CFSG.AGLEmbedding.R3.Co3Three.tcProg CFSG.AGLEmbedding.R3.Co3Three.tcSpec = true)
    ∧ (cpCheck (ops2 22) Co3Seed1 Co3Seed2 CFSG.AGLEmbedding.R3.Co3Three.cpNregs CFSG.AGLEmbedding.R3.Co3Three.cpProg CFSG.AGLEmbedding.R3.Co3Three.cpSpec = true)
    ∧ (CFSG.AGLEmbedding.R3.Co3Three.cpSpec.noFun = true) := KernelTc.cert9418

end Certificates
