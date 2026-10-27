module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenFacts
import Certificates.Kernel.Sporadic.Fi24Sev.Final
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

theorem certificate16952 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven.SevenFacts :=
  by
    intros
    exact CFSG.KD.Fi24Sev.Final.sevenFacts KernelFi24OrbL.bridge

end Certificates
