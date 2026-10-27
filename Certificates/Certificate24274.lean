module

public import Certificates.Kernel.SporSch.Mathieu.M22H1Final

public section

namespace Certificates

open CertificateChecks

theorem certificate24274 : (CFSG.EvenSporadicStandard.HypOne.M22.innerData = true) ∧
    (CFSG.EvenSporadicStandard.HypOne.M22.autData = true) ∧
    (CFSG.EvenSporadicStandard.HypOne.M22.e8Data = true) ∧
    (CFSG.EvenSporadicStandard.HypOne.M22.foursData = true) :=
  KernelSporSch.M22H1.facts

end Certificates
