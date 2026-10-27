module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2W
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Data
import Certificates.Kernel.Census.J2.Final

public section

namespace Certificates

open CertificateChecks

set_option maxRecDepth 100000 in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.J2 CFSG.KC.Census in
theorem certificate15007 : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)) (excs : List ExcRefP),
    RankTwoSporadic.J2.j2CheckWExc RankTwoSporadic.J2.j2E0 sG roots nodes cS wcs excs = true := KernelCensus.J2K.j2Exc_ok

end Certificates
