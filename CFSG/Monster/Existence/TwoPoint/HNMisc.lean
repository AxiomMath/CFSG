module

public import Certificates.Certificate6074

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem hnMiscCheck_ok :
    (∀ i ∈ List.range 5, wordLin (hnWU[i]! ++ hnWV[i]!) = 1) ∧
      (∀ i ∈ List.range 5, wordLin (hnWAlpha ++ hnWU[i]!) = wordLin (hnWU[i]! ++ hnWAlpha)) ∧
      (∀ i ∈ List.range 5, wordLin (hnWBeta ++ hnWU[i]!) = wordLin (hnWU[i]! ++ hnWBeta)) ∧
      wordLin hnWAB ≠ 1 ∧ wordLin hnWU[4]! ≠ 1 :=
  Certificates.certificate6074

end CFSG.Monster.Existence
