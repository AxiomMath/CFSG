module

public import CFSG.RankThree.PartOne.SPOR.Co1SylowGenData
import Certificates.Kernel.Co1Syl5.Glue
public import CFSG.RankThree.PartOne.SPOR.Co1SylowData

public section

namespace Certificates

open CFSG.RankThree.PartOne.SPOR in
theorem certificate1322150 : co1SylowGenOK co1SylowDerivs 41 39 = true :=
  CertificateChecks.KernelCo1Syl5.check

end Certificates
