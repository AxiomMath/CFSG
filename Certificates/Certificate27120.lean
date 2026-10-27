module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzInputs
import Certificates.Kernel.RuSz.Final

public section

namespace Certificates

theorem certificate27120 : CFSG.EvenSporadicStandard.Induction.RuSz.ruSzCheck = true :=
  CertificateChecks.KernelRuSz.ruSz_check

end Certificates
