module

public import Certificates.Certificate6082

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem thConjOrdCheck_ok :
    wordLin (thRhoT ++ thCAlpha) = wordLin (thCAlpha ++ thWAlpha) ∧
      wordLin (thRhoT ++ thCBeta) = wordLin (thCBeta ++ thWBeta) :=
  Certificates.certificate6082.1

theorem thThreeCCheck_ok :
    wordLin (wordThreeC ++ thWG) = wordLin (thWG ++ thWAB) :=
  Certificates.certificate6082.2

end CFSG.Monster.Existence
