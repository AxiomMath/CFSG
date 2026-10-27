module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12OverOdd
import Certificates.Kernel.LocalComp.M12Over.Odd
import Certificates.Kernel.LocalComp.M12Over.Cent

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.M12 in
theorem certificate15017 : m12OverFacts m12S :=
  ⟨KernelLC.M12Over.odd, KernelLC.M12Over.centOK, KernelLC.M12Over.hOK⟩

end Certificates
