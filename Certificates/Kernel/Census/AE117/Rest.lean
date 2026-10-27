module

public import Certificates.Data.GH74.AE117

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open Certificates.AE117

theorem cocCheck₅_eq : cocCheck₅ () = true := by decide +kernel
theorem cocCheck₆_eq : cocCheck₆ () = true := by decide +kernel
theorem cocCheck₇_eq : cocCheck₇ () = true := by decide +kernel
theorem genCheck₅_eq : genCheck₅ () = true := by decide +kernel
theorem genCheck₆_eq : genCheck₆ () = true := by decide +kernel
theorem genCheck₇_eq : genCheck₇ () = true := by decide +kernel
theorem spanCheck_five : spanCheck 5 () = true := by decide +kernel
theorem spanCheck_six : spanCheck 6 () = true := by decide +kernel
theorem spanCheck_seven : spanCheck 7 () = true := by decide +kernel

end CertificateChecks.KernelCensus
