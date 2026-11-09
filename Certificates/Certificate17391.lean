module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7GenGroup
import Certificates.Kernel.Sporadic.Fi7Perm.Final
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

theorem certificate17391 : CFSG.HardMathSupport.Dickson.I271.Fi7.Fi7Group :=
  CFSG.KD.Fi7Perm.Final.fi7Group KernelFi24OrbL.bridge

end Certificates
