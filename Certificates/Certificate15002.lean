
module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo3Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjW
import Certificates.Kernel.Census.Co3C.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Co3 CFSG.ComponentClassification.RankTwoSporadic.Cert
  CFSG.RankThree.Native CFSG.Monster.B.Co2.Native in
theorem certificate15002 : ∃ (inX inW : Array ℕ → Bool) (d : ConjData),
    (∀ a, validA 276 a = true → inX a = true → co3InP a = true) ∧
    (∀ a, validA 276 a = true → inW a = true →
      (co3InP a || co3InP (compA 276 (idA 276) a)) = true) ∧
    conjCensusOKW 276 co3PS inX (fun _ => true) inW false false false d #[] = true ∧
    d.xs.all inW = true ∧ d.xs.length = 10 := KernelCensus.Co3C.co3_conj

end Certificates
