
module


public import Certificates.Certificate6048

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem fiMiscCheck_ok :
    (∀ i ∈ List.range 10, wordLin (fiWAlpha ++ fiWU[i]!) = wordLin (fiWU[i]! ++ fiWAlpha)) ∧
      (∀ i ∈ List.range 10, wordLin (fiWBeta ++ fiWU[i]!) = wordLin (fiWU[i]! ++ fiWBeta)) ∧
      wordLin (fiWAlpha ++ fiWAlpha) = 1 ∧ wordLin (fiWBeta ++ fiWBeta) = 1 ∧
      wordLin (fiWAB ++ fiWAB ++ fiWAB) = 1 ∧ wordLin fiWAB ≠ 1 ∧ wordLin fiWU[3]! ≠ 1 :=
  Certificates.certificate6048

end CFSG.Monster.Existence
