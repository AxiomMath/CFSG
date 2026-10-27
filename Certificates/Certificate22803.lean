module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvCertInputs
public import Certificates.Certificate2022Base

public section

open CFSG.ComponentClassification.HSFLit.AutL34

namespace CertificateChecks.Batch22803

open CFSG.ComponentClassification.HSFLit.AutL34

private theorem unitNormOK_0 : unitNormOK (trL t0L) t0L = true := by decide +kernel

end CertificateChecks.Batch22803

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HSFLit.AutL34 in
theorem certificate22803 : unitNormOK (trL t0L) t0L = true := CertificateChecks.Batch22803.unitNormOK_0

end Certificates
