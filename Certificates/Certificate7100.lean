module

public import CFSG.Quasithin.H13.L32NKGCertInputs
import all CFSG.Quasithin.H13.L32NKGCertInputs

public section

namespace CertificateChecks.Batch7100

set_option maxHeartbeats 0 in
private theorem check_0 : CFSG.Quasithin.H13.KGCert.sp4QuadCheck = true := by
  decide +kernel

end CertificateChecks.Batch7100

namespace Certificates

open CertificateChecks

theorem certificate7100 : CFSG.Quasithin.H13.KGCert.sp4QuadCheck = true := CertificateChecks.Batch7100.check_0

end Certificates
