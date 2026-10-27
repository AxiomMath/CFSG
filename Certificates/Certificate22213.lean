module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsNonElemCertInputs
public import Certificates.Certificate2022Base

public section

open CFSG.ComponentClassification.GrSLit.L34Facts

namespace CertificateChecks.Batch22213

open CFSG.ComponentClassification.GrSLit.L34Facts

private theorem nonElemOK_eq_true_0 : nonElemOK = true := by
  decide +kernel

end CertificateChecks.Batch22213

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22213 : nonElemOK = true :=
  CertificateChecks.Batch22213.nonElemOK_eq_true_0

end Certificates
