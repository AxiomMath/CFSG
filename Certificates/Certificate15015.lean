module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12W
import Certificates.Kernel.Census.M12.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.M12 CFSG.KC.Census in
theorem certificate15015 : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)) (excs : List ExcRefP),
    m12CheckW m12S m12W m12E0 sG roots nodes cS wcs excs = true := KernelCensus.M12K.m12_ok

end Certificates
