module

public import Certificates.Certificate6083

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem thMiscCheck_ok :
    (∀ i ∈ List.range 8, wordLin (thWU[i]! ++ thWV[i]!) = 1) ∧ wordLin thWAB3 = 1 ∧
      wordLin thWAB ≠ 1 ∧ wordLin thWS7 = 1 ∧ wordLin thWU[5]! ≠ 1 :=
  Certificates.certificate6083

end CFSG.Monster.Existence
