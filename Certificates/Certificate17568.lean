module

public import Certificates.Kernel.Sporadic.Fi24FreeK.Group
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

theorem certificate17568_of_bridge
    (hB : 
      CFSG.KD.Fi24ThreeO.Group.Bridge) :
 CFSG.HardMathSupport.Dickson.I271.TabFi24.FreeFrameFacts :=
  CFSG.KD.Fi24FreeK.Group.freeFrameFacts_of hB

theorem certificate17568 : 
    CFSG.HardMathSupport.Dickson.I271.TabFi24.FreeFrameFacts :=
  certificate17568_of_bridge KernelFi24OrbL.bridge

end Certificates
