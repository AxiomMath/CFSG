module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ1W
import Certificates.Kernel.Census.J1.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.J1 CFSG.KC.Census in
theorem certificate15004 : ∃ (prog : List (ℕ × ℕ)) (sG : Array ℕ) (nodes : Array FNodeP) (cS : ArrCertP),
    j1CheckW prog sG nodes cS = true := KernelCensus.J1.j1_ok

end Certificates
