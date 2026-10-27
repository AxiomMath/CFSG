module

public import CFSG.Monster.Existence.TwoPoint.HNCheck
import Certificates.Kernel.KDenseP.TwoPoint.HN

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6074 : (∀ i ∈ List.range 5, wordLin (hnWU[i]! ++ hnWV[i]!) = 1) ∧
    (∀ i ∈ List.range 5, wordLin (hnWAlpha ++ hnWU[i]!) = wordLin (hnWU[i]! ++ hnWAlpha)) ∧
    (∀ i ∈ List.range 5, wordLin (hnWBeta ++ hnWU[i]!) = wordLin (hnWU[i]! ++ hnWBeta)) ∧
    wordLin hnWAB ≠ 1 ∧ wordLin hnWU[4]! ≠ 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6074

end Certificates
