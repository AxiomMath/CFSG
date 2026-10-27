module

public import Certificates.Certificate6089

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem thRelsCheck_ok_5 :
    ∀ i ∈ [1, 10, 12, 18, 24, 25, 26, 28, 30, 31, 34, 36],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 :=
  Certificates.certificate6089

end CFSG.Monster.Existence
