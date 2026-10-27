module

public import Certificates.Data.WE6Offender
import Certificates.Kernel.WE6OffK.Checks
import CFSG.Certificates.Kernel.WE6OffKSound

public section

namespace Certificates

open CertificateChecks.KernelWE6Off CFSG.KC.WE6K

open Certificates.WE6Offender in
theorem certificate709610 : check () = true :=
  check_of base (fun i hi => (rngK_iff.mp ord) i (Nat.zero_le i) hi) (all81 comm0 comm1 comm2)
    (all81 fix0 fix1 fix2) (all81 bound0 bound1 bound2)

end Certificates
