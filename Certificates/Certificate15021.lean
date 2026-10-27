module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNOTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNData
import Certificates.Kernel.Sporadic.OddCore.HNAG

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.HN in
theorem certificate15021 : hnAOCheck (decodePairsO hnAProgStr) hnAPregs (decodePairsO hnAPoolStr).toArray
      (decodeAO hnAWitStr) = true :=
  KernelSpor.HNAS.hnAO_ok

end Certificates
