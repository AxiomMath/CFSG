module

public import Certificates.Data.Fi24Rank.Fi22Check
import Certificates.Kernel.Fi22Rk.A431005

public section

namespace Certificates

open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative in
theorem certificate431005 : fi22RankOK () = true :=
  CertificateChecks.KernelFi22Rk.A.rank

end Certificates
