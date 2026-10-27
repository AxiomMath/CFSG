module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22W
import Certificates.Kernel.Census.M22II.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.M22 CFSG.KC.Census in
theorem certificate8043 : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)) (xg xs : Array ℕ) (xw : List (List ℕ)),
    m22CheckW false true sG roots nodes cS wcs xg xs xw = true := KernelCensus.M22II.m22II_ok

end Certificates
