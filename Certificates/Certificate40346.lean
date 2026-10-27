module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData6
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.F2
import Certificates.Kernel.MatCert.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.SectionRank.Native CFSG.Blueprint in
theorem certificate40346 : SClaim.check (ops2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2 j4_7_claims = true := KernelMC.j4Sec

end Certificates
