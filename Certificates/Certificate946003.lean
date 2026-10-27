module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertData
import all CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertData

public section

open CFSG.StandardType.StepTwoToralCert

namespace CertificateChecks.Batch946003

open CFSG.StandardType.StepTwoToralCert

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem check_0 : splitT0OK = true := by
  decide +kernel

end CertificateChecks.Batch946003

namespace Certificates

open CertificateChecks

open CFSG.StandardType.StepTwoToralCert in
theorem certificate946003 : splitT0OK = true := by
  exact CertificateChecks.Batch946003.check_0

end Certificates
