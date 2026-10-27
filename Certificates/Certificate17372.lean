module

public import Certificates.Data.RkBMFi24Inv
public import Certificates.Data.Kernel.Spor.Fi24OrbL
import Certificates.Kernel.Sporadic.Fi24Base.Glue
import Certificates.Kernel.Sporadic.Fi24OrbL.Bridge
import Certificates.Kernel.VecCert.HomBoundG

public section

namespace Certificates

open CertificateChecks

theorem certificate17372 : CFSG.HardMathSupport.Dickson.I271.RkBMFi24Inv.invCheck
    (CFSG.Sporadic.Fi24.orb) = true :=
  CFSG.KD.Fi24Base.invCheck_true KernelFi24OrbL.orb_alpha_orbL KernelFi24OrbL.orb_beta_orbL

end Certificates
