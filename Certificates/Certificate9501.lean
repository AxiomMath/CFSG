module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22ThreeData
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.TcGen.F3Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi22Three
  CFSG.Blueprint.NativeSporadic in
theorem certificate9501 : (tcCheck (ops3 77) Fi22Seed1 Fi22Seed2 CFSG.AGLEmbedding.R3.Fi22Three.tcNregs CFSG.AGLEmbedding.R3.Fi22Three.tcProg CFSG.AGLEmbedding.R3.Fi22Three.tcSpec = true)
    ∧ (cpCheck (ops3 77) Fi22Seed1 Fi22Seed2 CFSG.AGLEmbedding.R3.Fi22Three.cpNregs CFSG.AGLEmbedding.R3.Fi22Three.cpProg CFSG.AGLEmbedding.R3.Fi22Three.cpSpec = true)
    ∧ (CFSG.AGLEmbedding.R3.Fi22Three.cpSpec.noFun = true) := KernelTc.cert9501

end Certificates
