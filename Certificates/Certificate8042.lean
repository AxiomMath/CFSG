module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22W
import Certificates.Kernel.Census.M2217.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.M22 CFSG.KC.Census in
theorem certificate8042 : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)) (pfs : Array PerfWP) (xg xs : Array ℕ) (xw : List (List ℕ)),
    m22CheckW2 true false sG roots nodes cS wcs pfs xg xs xw = true := KernelCensus.M2217.m2217_ok

end Certificates
