module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaLyData
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.McertP.Glue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaLy
  CFSG.Blueprint.NativeSporadic in
theorem certificate9601 : modCheckW (opsP 5 111) LySeed1 LySeed2 lyNregs lyProg 3 lyMod
    lyTops lyTidx 7 lyCf lyCi lyCt = true := KernelMP.cert9601

end Certificates
