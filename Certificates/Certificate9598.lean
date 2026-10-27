module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaHNData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.McertP.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaHN
  CFSG.Blueprint.NativeSporadic in
theorem certificate9598 : modCheckE (opsP 5 133) HNSeed1 HNSeed2 hnNregs hnProg 3 hnMod
    hnTops hnGs hnCf hnCi hnCt = true := KernelMP.cert9598

end Certificates
