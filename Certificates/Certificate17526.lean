module

public import Certificates.Data.Fam3D42Local
public meta import Certificates.Data.Fam3D42Local
import Certificates.Kernel.D4.LocalUFacts
import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.D4LocalSound

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.Bal207.Fam3D42 in
theorem certificate17526 : localUCheck () = true :=
  KernelD4.localU_ok

end Certificates
