module

public import Certificates.Certificate6080

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem thCommAlphaCheck_ok :
    ∀ i ∈ List.range 8, wordLin (thWAlpha ++ thWU[i]!) = wordLin (thWU[i]! ++ thWAlpha) :=
  Certificates.certificate6080

end CFSG.Monster.Existence
