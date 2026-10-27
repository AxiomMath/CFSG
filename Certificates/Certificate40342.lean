module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData3
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.Fp
import Certificates.Kernel.McertP.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.SectionRank.Native CFSG.Blueprint in
theorem certificate40342 : BClaim.check (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 ly_7_claims = true := KernelMP.cert40342

end Certificates
