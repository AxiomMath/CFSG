module

public import Certificates.Data.E6Heart
public meta import Certificates.Data.E6Heart
import all Certificates.Data.E6Heart

public section

open Certificates.E6Heart

namespace CertificateChecks.Batch712501

open Certificates.E6Heart

set_option maxHeartbeats 0 in
private theorem e6_heart_check_0 : check () = true := by
  decide +kernel

end CertificateChecks.Batch712501

namespace Certificates

open Certificates.E6Heart in
theorem certificate712501 : check () = true := by
  exact CertificateChecks.Batch712501.e6_heart_check_0

end Certificates
