module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM24C
import Certificates.Kernel.Census.M24C.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.M24 CFSG.ComponentClassification.RankTwoSporadic.Cert in
theorem certificate8045 : ∃ (xg xs : Array (Array ℕ)) (xw : List (List ℕ)) (d : ConjData)
      (e0 : Array (Array ℕ)) (wit : Wit) (cl : ClosW),
    m24CheckC xg xs xw d e0 wit cl = true := KernelCensus.M24C.m24_conj

end Certificates
