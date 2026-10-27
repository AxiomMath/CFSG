module

public import Certificates.Data.GrSLitL34FactsFourCubeData

public section

open CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

namespace CertificateChecks.Batch22216

open CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem complementOK_eq_true_0 : complementOK = true := by
  decide +kernel

end CertificateChecks.Batch22216

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Facts.FourCube in
theorem certificate22216 : complementOK = true :=
  CertificateChecks.Batch22216.complementOK_eq_true_0

end Certificates
