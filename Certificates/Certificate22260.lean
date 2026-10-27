module

public import Certificates.Data.SolMaxEightPerm
import Certificates.Kernel.SolMax.EightPermF

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.SolMax.EightPerm in
theorem certificate22260 : eightPermCheck = true :=
  KernelSolMax.EightPerm.eightPerm_true

end Certificates
