
module

public import CFSG.Sporadic.Fi24.Fi24EFacts
import Certificates.Kernel.Sporadic.Fi24E.Group
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

theorem certificate10510 : 
    CFSG.Sporadic.Fi24.Fi24EFacts :=
  CFSG.KD.Fi24E.Group.facts_of KernelFi24OrbL.bridge

end Certificates
