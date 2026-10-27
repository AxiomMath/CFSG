module

public import CFSG.RankThree.PartOne.SPOR.Co1SylowData
import Certificates.Kernel.Co1Syl5.Glue14962

public section

namespace Certificates

open CFSG.RankThree.PartOne.SPOR in
theorem certificate14962 : co1SylowOK co1SylowDerivs 41 39 42 = true :=
  CertificateChecks.KernelCo1Syl5.check14962

end Certificates
