
module

public import Certificates.Certificate1016Base
import all Certificates.Certificate1016Base

public import Certificates.Kernel.Sporadic.Fi24OrbL.FactsPrelude

public section

namespace Certificates

theorem certificate1016 : CFSG.Sporadic.Fi24.CoreFacts :=
  CertificateChecks.KernelFi24OrbL.core_facts_proved

end Certificates
