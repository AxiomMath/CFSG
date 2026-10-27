module

public import Certificates.Data.Fi24Rank.KCheck
import Certificates.Kernel.Fi24Rk.A431006

public section

namespace Certificates

open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative in
theorem certificate431006 : kRankOK () = true :=
  CertificateChecks.KernelFi24Rk.A.rank

end Certificates
