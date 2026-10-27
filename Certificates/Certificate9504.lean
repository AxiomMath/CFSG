module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONThreeData
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.TcGen.F3Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.ONThree
  CFSG.Blueprint.NativeSporadic in
theorem certificate9504 : (tcCheck (ops3 154) ONSeed1 ONSeed2 CFSG.AGLEmbedding.R3.ONThree.tcNregs CFSG.AGLEmbedding.R3.ONThree.tcProg CFSG.AGLEmbedding.R3.ONThree.tcSpec = true)
    ∧ (cpCheck (ops3 154) ONSeed1 ONSeed2 CFSG.AGLEmbedding.R3.ONThree.cpNregs CFSG.AGLEmbedding.R3.ONThree.cpProg CFSG.AGLEmbedding.R3.ONThree.cpSpec = true)
    ∧ (CFSG.AGLEmbedding.R3.ONThree.cpSpec.noFun = true) := KernelTc.cert9504

end Certificates
