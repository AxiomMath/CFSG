module

public import Certificates.Kernel.Sporadic.Fi24FreeK.Group
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

theorem certificate17569_of_bridge
    (hB : 
      CFSG.KD.Fi24ThreeO.Group.Bridge) :
 CFSG.HardMathSupport.Dickson.I271.TabFi24.FreeLamFacts :=
  CFSG.KD.Fi24FreeK.Group.freeLamFacts_of hB

theorem certificate17569 : 
    CFSG.HardMathSupport.Dickson.I271.TabFi24.FreeLamFacts :=
  certificate17569_of_bridge KernelFi24OrbL.bridge

end Certificates
