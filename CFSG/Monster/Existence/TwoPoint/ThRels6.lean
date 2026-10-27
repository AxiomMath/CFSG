module

public import Certificates.Certificate6090

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem thRelsCheck_ok_6 :
    ∀ i ∈ [4, 6, 11, 15, 17, 20, 21, 23, 27, 29],
      wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 :=
  Certificates.certificate6090

end CFSG.Monster.Existence
