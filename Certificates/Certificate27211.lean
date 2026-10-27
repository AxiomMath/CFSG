module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelMatch
import Certificates.Kernel.G24Match.C27211

public section

namespace Certificates

open CFSG.EvenSporadicStandard.G24Model in
theorem certificate27211 : matchOK = true :=
  CertificateChecks.KernelG24.Match27211.matchOK_true

end Certificates
