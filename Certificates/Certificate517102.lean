module

public import Certificates.Data.S7SocU33

public section

open Certificates.S7SocU33

namespace CertificateChecks.Batch517102

open Certificates.S7SocU33

set_option maxHeartbeats 0 in
private theorem u33_soc_517102_0 : u33SocCheck () = true := by
  decide +kernel

end CertificateChecks.Batch517102

namespace Certificates

open CertificateChecks

open Certificates.S7SocU33 in
theorem certificate517102 : u33SocCheck () = true :=
  CertificateChecks.Batch517102.u33_soc_517102_0

end Certificates
