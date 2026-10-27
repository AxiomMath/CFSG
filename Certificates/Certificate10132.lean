module

public import Certificates.Data.Fi24ThreeFix
public import Certificates.Data.Kernel.Spor.Fi24OrbL
import Certificates.Kernel.Sporadic.Fi24Base.Glue
import Certificates.Kernel.Sporadic.Fi24OrbL.Bridge
import Certificates.Kernel.VecCert.HomBoundG

public section

namespace Certificates

open CertificateChecks

theorem certificate10132 : Timmesfeld.Fi24Cl.fi24RepFixOK (CFSG.Sporadic.Fi24.orb) = true :=
  CFSG.KD.Fi24Base.fi24RepFixOK_true KernelFi24OrbL.orb_alpha_orbL KernelFi24OrbL.orb_beta_orbL

end Certificates
