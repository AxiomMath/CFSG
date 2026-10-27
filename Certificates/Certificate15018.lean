module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU42W
import Certificates.Kernel.Census.U42.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoHypIICover.U42 CFSG.KC.Census in
theorem certificate15018 : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)), u42CheckW sG roots nodes cS wcs = true := KernelCensus.U42K.u42_ok

end Certificates
