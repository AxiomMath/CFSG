module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SuzThreeData
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.TcGen.F3Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.SuzThree
  CFSG.Blueprint.NativeSporadic in
theorem certificate9500 : (tcCheck (ops3 64) SuzSeed1 SuzSeed2 CFSG.AGLEmbedding.R3.SuzThree.tcNregs CFSG.AGLEmbedding.R3.SuzThree.tcProg CFSG.AGLEmbedding.R3.SuzThree.tcSpec = true)
    ∧ (cpCheck (ops3 64) SuzSeed1 SuzSeed2 CFSG.AGLEmbedding.R3.SuzThree.cpNregs CFSG.AGLEmbedding.R3.SuzThree.cpProg CFSG.AGLEmbedding.R3.SuzThree.cpSpec = true)
    ∧ (CFSG.AGLEmbedding.R3.SuzThree.cpSpec.noFun = true) := KernelTc.cert9500

end Certificates
