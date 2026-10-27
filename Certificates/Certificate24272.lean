module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M24Inputs
import Certificates.Kernel.SporSch.Mathieu.M24H1Facts

public section

namespace Certificates

theorem certificate24272 : (CFSG.EvenSporadicStandard.HypOne.M24.fourData = true) ∧
    (CFSG.EvenSporadicStandard.HypOne.M24.e8Data = true) :=
  CertificateChecks.KernelSporSch.M24H1.facts

end Certificates
