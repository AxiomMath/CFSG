module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HNThreeData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.TcGen.F5Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.HNThree
  CFSG.Blueprint.NativeSporadic in
theorem certificate9506 : (tcCheck (opsP 5 133) HNSeed1 HNSeed2 CFSG.AGLEmbedding.R3.HNThree.tcNregs CFSG.AGLEmbedding.R3.HNThree.tcProg CFSG.AGLEmbedding.R3.HNThree.tcSpec = true)
    ∧ (cpCheck (opsP 5 133) HNSeed1 HNSeed2 CFSG.AGLEmbedding.R3.HNThree.cpNregs CFSG.AGLEmbedding.R3.HNThree.cpProg CFSG.AGLEmbedding.R3.HNThree.cpSpec = true)
    ∧ (CFSG.AGLEmbedding.R3.HNThree.cpSpec.noFun = true) := KernelTc.cert9506

end Certificates
