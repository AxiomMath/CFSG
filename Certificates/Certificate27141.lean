module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzOrderEightCheck
import Certificates.Kernel.Co2Chain.Suz27141

public section

namespace Certificates

theorem certificate27141 : CFSG.EvenSporadicStandard.Induction.suzOrderEightCheck = true :=
  CertificateChecks.KernelCo2Chain.Suz27141.check

end Certificates
