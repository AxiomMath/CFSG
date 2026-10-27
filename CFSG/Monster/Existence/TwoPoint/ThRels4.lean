module

public import Certificates.Certificate6088

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem thRelsCheck_ok_4 :
    ∀ i ∈ [3, 8, 9, 16, 19, 22],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 :=
  Certificates.certificate6088

end CFSG.Monster.Existence
