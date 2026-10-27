module

public import Certificates.Kernel.Sporadic.Fi24TwinK.Group
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

theorem certificate17567 : 
    CFSG.HardMathSupport.Dickson.I271.TabFi24.TwinFacts [16] :=
  by
    intros
    exact CFSG.KD.Fi24TwinK.Group.twinFacts_of (r := 2) KernelFi24OrbL.bridge (by norm_num)

end Certificates
