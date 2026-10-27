module

public import CFSG.Quasithin.H13.L32NKGCertInputs
import all CFSG.Quasithin.H13.L32NKGCertInputs

public section

namespace CertificateChecks.Batch7101

private theorem check_0 : CFSG.Quasithin.H13.KGCert.sp4LineCheck = true := by
  decide +kernel

end CertificateChecks.Batch7101

namespace Certificates

open CertificateChecks

theorem certificate7101 : CFSG.Quasithin.H13.KGCert.sp4LineCheck = true := CertificateChecks.Batch7101.check_0

end Certificates
