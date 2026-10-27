module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M23Inputs
import Certificates.Kernel.SporSch.Mathieu.M23H1Facts

public section

namespace Certificates

theorem certificate24271 : (CFSG.EvenSporadicStandard.HypOne.M23.fourData = true) ∧
    (CFSG.EvenSporadicStandard.HypOne.M23.e8Data = true) :=
  CertificateChecks.KernelSporSch.M23H1.facts

end Certificates
