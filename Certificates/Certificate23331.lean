module

public import Certificates.Data.SolMaxL34Graph
import Certificates.Kernel.LocalComp.L34T1.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.SolMax.L34Graph in
theorem certificate23331 : l34GraphUnitaryCheck = true := KernelLC.L34T1.gu_true

end Certificates
