module

public import Certificates.Data.Fam3D42
public meta import Certificates.Data.Fam3D42
import Certificates.Kernel.D4.L3Facts
import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.Bal207.Fam3D42 in
theorem certificate17525 : caseA3Check () = true :=
  KernelD4.caseA3_ok

end Certificates
