module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Group
import Certificates.Kernel.Sporadic.Fi24KPerm.Final
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

theorem certificate753522 : CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Fi24KGroup :=
  CFSG.KD.Fi24KPerm.Final.fi24kGroup KernelFi24OrbL.bridge

end Certificates
