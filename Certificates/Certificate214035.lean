module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenFacts
import Certificates.Kernel.Sporadic.Fi24Sev.Final
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

theorem certificate214035 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven.CentFacts :=
  by
    intros
    exact CFSG.KD.Fi24Sev.Final.centFacts KernelFi24OrbL.bridge

end Certificates
