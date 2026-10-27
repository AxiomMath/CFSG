module

public import Certificates.Kernel.Sporadic.Fi24TwinK.Group
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

theorem certificate17565 : 
    CFSG.HardMathSupport.Dickson.I271.TabFi24.TwinFacts [14, 16, 16, 14, 16, 16] :=
  by
    intros
    exact CFSG.KD.Fi24TwinK.Group.twinFacts_of (r := 0) KernelFi24OrbL.bridge (by norm_num)

end Certificates
