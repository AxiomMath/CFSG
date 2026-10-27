module

public import Certificates.Data.A3LatticeF4
public meta import Certificates.Data.A3LatticeF4

public section

open Certificates.A3LatticeF4

namespace CertificateChecks.Batch715501

open Certificates.A3LatticeF4

set_option maxHeartbeats 0 in
private theorem a3_f4_check_0 : check () = true := by
  decide +kernel

end CertificateChecks.Batch715501

namespace Certificates

open Certificates.A3LatticeF4 in
theorem certificate715501 : check () = true := by
  exact CertificateChecks.Batch715501.a3_f4_check_0

end Certificates
