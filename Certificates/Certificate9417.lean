module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLThreeData
public import Certificates.Data.CFSGNative.CTP.StrongP
import Certificates.Kernel.TcGen.F3Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.McLThree in
theorem certificate9417 : (tcCheck (ops3 21) mclSylow5Data.seedA mclSylow5Data.seedB CFSG.AGLEmbedding.R3.McLThree.tcNregs CFSG.AGLEmbedding.R3.McLThree.tcProg CFSG.AGLEmbedding.R3.McLThree.tcSpec = true)
    ∧ (cpCheck (ops3 21) mclSylow5Data.seedA mclSylow5Data.seedB CFSG.AGLEmbedding.R3.McLThree.cpNregs CFSG.AGLEmbedding.R3.McLThree.cpProg CFSG.AGLEmbedding.R3.McLThree.cpSpec = true)
    ∧ (CFSG.AGLEmbedding.R3.McLThree.cpSpec.noFun = true) := KernelTc.cert9417

end Certificates
