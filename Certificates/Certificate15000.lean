
module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHSTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjW
import Certificates.Kernel.Census.HSC.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.HS CFSG.ComponentClassification.RankTwoSporadic.Cert
  CFSG.RankThree.Native CFSG.Monster.B.Co2.Native in
theorem certificate15000 : ∃ (inX inW : Array ℕ → Bool) (d : ConjData),
    (∀ a, validA 100 a = true → inX a = true → hsInP a = true) ∧
    (∀ a, validA 100 a = true → inW a = true →
      (hsInP a || hsInP (compA 100 (hs100Arr 15) a)) = true) ∧
    conjCensusOKW 100 hsPS inX (fun _ => true) inW false false false d #[] = true ∧
    d.xs.all inW = true ∧ d.xs.length = 10 := KernelCensus.HSC.hs_conj

end Certificates
