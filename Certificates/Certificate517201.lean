module

public import Certificates.Data.S7TwinSp6
import Certificates.Kernel.S7TwinSp6.Facts

public section

namespace Certificates

open CertificateChecks

open Certificates.S7TwinSp6 in
theorem certificate517201 : sp6TwinSylow () = true ∧ sp6TwinReps () = true ∧ sp6TwinK0 () = true ∧
    sp6TwinPairs () = true := KernelS7Sp6.facts517201

end Certificates
