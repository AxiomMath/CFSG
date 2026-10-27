module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCertInputs
public import Certificates.Certificate2022Base

public section

open CFSG.ComponentClassification.HSFLit.AutL34

namespace CertificateChecks.Batch23960

open CFSG.ComponentClassification.HSFLit.AutL34

private theorem unitCommOK_0 : unitCommOK (trL t0L) t0L = true := by decide +kernel

end CertificateChecks.Batch23960

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HSFLit.AutL34 in
theorem certificate23960 : unitCommOK (trL t0L) t0L = true := CertificateChecks.Batch23960.unitCommOK_0

end Certificates
