module

public import Certificates.Data.SuzLmRank
import Certificates.Kernel.LocalComp.SuzLmF

public section

namespace Certificates

open CertificateChecks

theorem certificate10147 : CFSG.LocalAnalysis.GLTheoremA.H1017.SuzLm.lmRankOK () = true := KernelLC.SuzLm.rank_true

end Certificates
