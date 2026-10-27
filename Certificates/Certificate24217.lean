module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.TransvConjData
import CFSG.Certificates.Kernel.TransvKSound
import Certificates.Kernel.TransvK.Check

public section

namespace Certificates

open CertificateChecks

theorem certificate24217 : CFSG.EvenSporadicStandard.ThStd.LocalDataTh.TFacts = true :=
  CFSG.KC.TransvK.TFacts_of KernelTransvK.TFactsA_ok

end Certificates
