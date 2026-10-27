module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM23W
import Certificates.Kernel.Census.M23.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.M23 CFSG.KC.Census in
theorem certificate8044 : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)) (pfs : Array PerfWP),
    m23CheckW2 sG roots nodes cS wcs pfs = true := KernelCensus.M23K.m23_ok

end Certificates
