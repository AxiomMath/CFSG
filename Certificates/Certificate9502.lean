module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Co1FiveData
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.TcGen.F2Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Co1Five
  CFSG.Blueprint.NativeSporadic in
theorem certificate9502 : (tcCheck (ops2 24) Co1Seed1 Co1Seed2 CFSG.AGLEmbedding.R3.Co1Five.tcNregs CFSG.AGLEmbedding.R3.Co1Five.tcProg CFSG.AGLEmbedding.R3.Co1Five.tcSpec = true)
    ∧ (cpCheck (ops2 24) Co1Seed1 Co1Seed2 CFSG.AGLEmbedding.R3.Co1Five.cpNregs CFSG.AGLEmbedding.R3.Co1Five.cpProg CFSG.AGLEmbedding.R3.Co1Five.cpSpec = true)
    ∧ (CFSG.AGLEmbedding.R3.Co1Five.cpSpec.noFun = true) := KernelTc.cert9502

end Certificates
