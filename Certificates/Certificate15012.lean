module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIIW
import Certificates.Kernel.Census.L34

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoL3Four.HypII CFSG.KC.Census in
theorem certificate15012 : ∃ (prog : List (ℕ × ℕ)) (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)), l34CheckWII prog sG roots nodes cS wcs = true :=
  ⟨_, _, _, _, _, _, KernelCensus.L34K.l34CheckWII_eq_true⟩

end Certificates
