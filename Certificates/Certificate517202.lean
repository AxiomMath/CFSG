module

public import Certificates.Data.S7TwinO8
import Certificates.Kernel.O8Twin.Facts

public section

namespace Certificates

open CertificateChecks

open Certificates.S7TwinO8 in
theorem certificate517202 : o8TwinGens () = true ∧ o8TwinSylow () = true ∧ o8TwinReps () = true ∧
    o8TwinK0 () = true ∧ o8TwinPairs () = true := KernelO8Twin.facts517202

end Certificates
