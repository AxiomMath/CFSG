module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB1Inputs
import Certificates.Kernel.SporSch.Ru.Pair

public section

namespace Certificates

open CertificateChecks

theorem certificate24920 : CFSG.EvenSporadicStandard.RuStd.ruPairCheck = true :=
  KernelSporSch.RuPair.pairCheck

end Certificates
