module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData4
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.Fp
import Certificates.Kernel.McertP.ONGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.SectionRank.Native CFSG.Blueprint in
theorem certificate40343 : GClaim.check (opsP 3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2 on_5_claims = true := KernelMP.cert40343

end Certificates
