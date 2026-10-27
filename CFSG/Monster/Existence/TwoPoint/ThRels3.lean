module

public import Certificates.Certificate6087

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem thRelsCheck_ok_3 :
    ∀ i ∈ [5, 32, 37],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 :=
  Certificates.certificate6087

end CFSG.Monster.Existence
