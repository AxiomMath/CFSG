module

public import CFSG.GF2Type.Smith1979.GammaU.ResConjInputs
import Certificates.Kernel.Census.GammaU.C16970
import CFSG.Certificates.Kernel.GammaUListSound

public section

namespace Certificates

open CertificateChecks

open CFSG.GF2Type.Smith1979.GammaU.StepA in
theorem certificate16970 : resConjCheck () = true :=
  Certificates.Kernel.GammaUList.resConjCheck_of KernelCensus.resConjCheckL_eq

end Certificates
