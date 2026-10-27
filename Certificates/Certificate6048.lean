
module


public import CFSG.Monster.Existence.TwoPoint.Fi23Check
import Certificates.Kernel.KDenseP.TwoPoint.Fi

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6048 : (∀ i ∈ List.range 10, wordLin (fiWAlpha ++ fiWU[i]!) = wordLin (fiWU[i]! ++ fiWAlpha)) ∧
    (∀ i ∈ List.range 10, wordLin (fiWBeta ++ fiWU[i]!) = wordLin (fiWU[i]! ++ fiWBeta)) ∧
    wordLin (fiWAlpha ++ fiWAlpha) = 1 ∧ wordLin (fiWBeta ++ fiWBeta) = 1 ∧
    wordLin (fiWAB ++ fiWAB ++ fiWAB) = 1 ∧ wordLin fiWAB ≠ 1 ∧ wordLin fiWU[3]! ≠ 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6048

end Certificates
