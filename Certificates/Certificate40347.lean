module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData7
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.Fp
import Certificates.Kernel.MatCert.HN11.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.SectionRank.Native CFSG.Blueprint in
theorem certificate40347 : SClaim.check (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 hn_11_claims = true := KernelMC.HN11.sec

end Certificates
