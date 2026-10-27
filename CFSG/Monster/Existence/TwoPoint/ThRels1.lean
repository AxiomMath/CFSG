module

public import Certificates.Certificate6085

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem thRelsCheck_ok_1 :
    ∀ i ∈ [0, 2, 33, 35],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 :=
  Certificates.certificate6085

end CFSG.Monster.Existence
