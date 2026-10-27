module

public import CFSG.Sporadic.Co2Smith.GlRefineFacts
import Certificates.Kernel.Co2Smith.Ref
public import CFSG.Sporadic.Co2Smith.GlDataInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2Smith in
theorem certificate21121 :
    GlOrbitFacts [Native.glPermArr Native.glAl, Native.glPermArr Native.glGa]
      (Native.glWit0.map (·.1)) (Native.glWit1.map (·.1)) (Native.glWit2.map (·.1))
      [(1172, Native.glWit0Pts 1), (1348, Native.glWit0Pts 2)] := KernelCo2Smith.refC0_facts

end Certificates
