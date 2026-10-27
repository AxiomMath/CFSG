module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cCertInputs60

public section

open CFSG.ComponentClassification.HSFLit.KD8c

namespace CertificateChecks.Batch22801

open CFSG.ComponentClassification.HSFLit.KD8c

private theorem chk60_0 : chk60 = true := by decide +kernel

end CertificateChecks.Batch22801

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HSFLit.KD8c in
theorem certificate22801 : chk60 = true := by
  exact CertificateChecks.Batch22801.chk60_0

end Certificates
