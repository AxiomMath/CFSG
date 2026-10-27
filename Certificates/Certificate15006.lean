module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2W
import Certificates.Kernel.Census.J2.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.J2 CFSG.KC.Census in
theorem certificate15006 : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)), RankTwoSporadic.J2.j2CheckWII sG roots nodes cS wcs = true := KernelCensus.J2K.j2II_ok

end Certificates
