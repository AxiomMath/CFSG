module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J2Inputs
import Certificates.Kernel.J2HypOne.Final

public section

namespace Certificates

theorem certificate24273 : (CFSG.EvenSporadicStandard.HypOne.J2.e8Data = true) ∧
    (CFSG.EvenSporadicStandard.HypOne.J2.foursData = true) :=
  CertificateChecks.KernelJ2HypOne.facts

end Certificates
