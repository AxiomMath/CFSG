module

public import Certificates.Kernel.Sporadic.Fi24Oct.Group
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

theorem certificate7059_of_bridge
    (hB : 
      CFSG.KD.Fi24ThreeO.Group.Bridge) :
 CFSG.Sporadic.Fi24.OctadFacts :=
  CFSG.KD.Fi24Oct.Group.octadFacts_of hB

theorem certificate7059 : 
    CFSG.Sporadic.Fi24.OctadFacts :=
  certificate7059_of_bridge KernelFi24OrbL.bridge

end Certificates
