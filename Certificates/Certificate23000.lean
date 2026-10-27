module

public import Certificates.Data.GSThmBCatalog7SuzCS
import Certificates.Kernel.Sporadic.OddCore.Suz23000F

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.CatFactsL4U4.SuzCS in
theorem certificate23000 : betaOK = true ∧ outerOK = true ∧ pinOK = true :=
  KernelSpor.Suz23000.check23000

end Certificates
