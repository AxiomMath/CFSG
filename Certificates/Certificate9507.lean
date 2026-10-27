module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi23ThreeData
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.TcGen.Fi23Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi23Three
  CFSG.Blueprint.NativeSporadic in
theorem certificate9507 : (tcCheck (ops3 253) Fi23Seed1 Fi23Seed2 CFSG.AGLEmbedding.R3.Fi23Three.tcNregs CFSG.AGLEmbedding.R3.Fi23Three.tcProg CFSG.AGLEmbedding.R3.Fi23Three.tcSpec = true)
    ∧ (cpCheck (ops3 253) Fi23Seed1 Fi23Seed2 CFSG.AGLEmbedding.R3.Fi23Three.cpNregs CFSG.AGLEmbedding.R3.Fi23Three.cpProg CFSG.AGLEmbedding.R3.Fi23Three.cpSpec = true)
    ∧ (CFSG.AGLEmbedding.R3.Fi23Three.cpSpec.noFun = true) := KernelTc.cert9507

end Certificates
