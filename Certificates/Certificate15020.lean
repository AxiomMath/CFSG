module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNData
public import Certificates.Kernel.SporSch.HN.Pt15020
import Certificates.Certificate2099
import Certificates.Certificate2100
import Certificates.Certificate2102

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.HN in
theorem certificate15020 : hnT4Check (decodePoolT4 hnT4PoolStr) (decodeT4 hnT4WitStr) = true :=
  KernelSporSch.HNPt15020.hn_t4_ok

end Certificates
