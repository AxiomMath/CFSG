module

public import Certificates.Certificate6081

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem thCommBetaCheck_ok :
    ∀ i ∈ List.range 8, wordLin (thWBeta ++ thWU[i]!) = wordLin (thWU[i]! ++ thWBeta) :=
  Certificates.certificate6081

end CFSG.Monster.Existence
