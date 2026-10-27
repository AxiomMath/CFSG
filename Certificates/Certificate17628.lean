module

public import CFSG.HardMathSupport.Dickson.Bal207.D42TriInputs
import Certificates.Kernel.D42Tri.RhoGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.Bal207.D42Tri in
theorem certificate17628 : rhoClassCheck = true :=
  KernelD42Tri.rhoClass_ok

end Certificates
