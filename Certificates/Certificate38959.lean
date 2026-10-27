module

public import Certificates.Data.GF2W1112Co2U

public section

namespace CertificateChecks.Batch38959

set_option maxHeartbeats 0 in
private theorem check_0 : CFSG.GF2W1112.w12UCheck3 () = true := by
  decide +kernel

end CertificateChecks.Batch38959

namespace Certificates

open CertificateChecks

theorem certificate38959 : CFSG.GF2W1112.w12UCheck3 () = true :=
  CertificateChecks.Batch38959.check_0

end Certificates
