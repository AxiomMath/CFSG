module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeClasses
import Certificates.Kernel.Sporadic.Fi24Pc.Glue
import Certificates.Kernel.Sporadic.Fi24OrbL.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate13693 : 
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Fi24ThreeClasses :=
  by
    intros
    exact CFSG.KD.Fi24Pc.fi24ThreeClasses_of_letters KernelFi24OrbL.pairG_LN

end Certificates
