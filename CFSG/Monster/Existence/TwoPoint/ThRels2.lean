module

public import Certificates.Certificate6086

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem thRelsCheck_ok_2 :
    ∀ i ∈ [7, 14, 38],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 :=
  Certificates.certificate6086

end CFSG.Monster.Existence
