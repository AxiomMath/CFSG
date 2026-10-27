module

public import Certificates.Data.SmithD6Tr7

public section

namespace CertificateChecks.Batch38790

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem tr7ChkClass_holds_0 : CFSG.SmithD6.tr7ChkClass = true := by
  decide +kernel

end CertificateChecks.Batch38790

namespace Certificates

open CertificateChecks

theorem certificate38790 : CFSG.SmithD6.tr7ChkClass = true :=
  CertificateChecks.Batch38790.tr7ChkClass_holds_0

end Certificates
