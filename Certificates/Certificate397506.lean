module

public import Certificates.Data.TwinPerpSmSp1WitJ3
import Certificates.Kernel.Q8Wit.J3Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate397506 : TwinPerpSmSp1.q8WitCheck TwinPerpSmSp1.j3Wit = true := KernelQ8W.J3.q8Wit_true

end Certificates
