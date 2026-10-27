module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34OrbitCertInputs
public import Certificates.Certificate2022Base

public section

open CFSG.ComponentClassification.HSFLit.AutL34

namespace CertificateChecks.Batch22805

open CFSG.ComponentClassification.HSFLit.AutL34

private theorem cosetClassOK_0 : cosetClassOK (trL t0L) t0L = true := by decide +kernel

end CertificateChecks.Batch22805

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HSFLit.AutL34 in
theorem certificate22805 : cosetClassOK (trL t0L) t0L = true := CertificateChecks.Batch22805.cosetClassOK_0

end Certificates
