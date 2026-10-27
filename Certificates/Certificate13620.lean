
module


public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22ThreeInputs
import Certificates.Kernel.Fi22Cls.Final

public section

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi22.Native in
theorem certificate13620 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native.classifyOK
    (CFSG.Sporadic.Fi22.Native.orbitData ()) = true :=
  CertificateChecks.KernelFi22Cls.classifyOK_true

end Certificates
