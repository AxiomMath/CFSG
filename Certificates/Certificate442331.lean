module

public import Certificates.Data.S8DFin

public section

namespace Certificates

set_option maxHeartbeats 0 in
theorem certificate442331 : S8DFin.check () = true := by decide +kernel

end Certificates
