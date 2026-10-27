module

public import Certificates.Data.E64PresModel
import all Certificates.Data.E64PresModel

public section

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64P

namespace CertificateChecks.Batch550872

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64P

set_option maxHeartbeats 0 in
private theorem rowsCheck_holds : rowsCheck () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem relModelCheck_holds : relModelCheck () = true := by
  decide +kernel

end CertificateChecks.Batch550872

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64P in
theorem certificate550872 : rowsCheck () = true ∧ relModelCheck () = true :=
  ⟨CertificateChecks.Batch550872.rowsCheck_holds, CertificateChecks.Batch550872.relModelCheck_holds⟩

end Certificates
