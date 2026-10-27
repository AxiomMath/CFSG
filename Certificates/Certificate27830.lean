module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAdmGen
public import Certificates.Certificate27820

public section

namespace CertificateChecks.Batch27830

theorem admGenCheck_0 : CFSG.EvenSporadicStandard.Fin76b.W16.admGenCheck = true := by
  decide +kernel

end CertificateChecks.Batch27830

namespace Certificates

open CertificateChecks

theorem certificate27830 : CFSG.EvenSporadicStandard.Fin76b.W16.admGenCheck = true := CertificateChecks.Batch27830.admGenCheck_0

end Certificates
