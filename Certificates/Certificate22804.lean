module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34PairCertInputs
public import Certificates.Certificate2022Base

public section

open CFSG.ComponentClassification.HSFLit.AutL34

namespace CertificateChecks.Batch22804

open CFSG.ComponentClassification.HSFLit.AutL34

private theorem sqCenterOK_0 : sqCenterOK t0L = true := by decide +kernel

end CertificateChecks.Batch22804

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HSFLit.AutL34 in
theorem certificate22804 : sqCenterOK t0L = true := CertificateChecks.Batch22804.sqCenterOK_0

end Certificates
