module

public import CFSG.Sporadic.Co2Smith.GlRefineFacts
import Certificates.Kernel.Co2Smith.Ref
public import CFSG.Sporadic.Co2Smith.GlDataInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2Smith in
theorem certificate21122 :
    GlOrbitFacts [Native.glPermArr Native.glAl, Native.glPermArr Native.glGa,
      Native.glPermArr Native.glZ] (Native.glWitZ0.map (·.1)) (Native.glWitZ1.map (·.1))
      (Native.glWitZ2.map (·.1)) [] := KernelCo2Smith.refCz_facts

end Certificates
