module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData5
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.Fp
import Certificates.Kernel.McertP.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.SectionRank.Native CFSG.Blueprint in
theorem certificate40345 : GClaim.check (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 hn_7_claims = true := KernelMP.cert40345

end Certificates
