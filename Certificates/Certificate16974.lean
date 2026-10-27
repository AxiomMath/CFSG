module

public import CFSG.GF2Type.Smith1979.GammaU.SingCountInputs
import Certificates.Kernel.Census.Small.C16974

public section

namespace Certificates

open CertificateChecks

open CFSG.GF2Type.Smith1979.GammaU in
theorem certificate16974 : singCount () = true := KernelCensus.check16974

end Certificates
