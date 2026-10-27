module

public import Certificates.Certificate6084

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem thRelsCheck_ok_0 :
    ∀ i ∈ [13],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 :=
  Certificates.certificate6084

end CFSG.Monster.Existence
