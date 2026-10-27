module

public import Certificates.Certificate6073

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem hnConjOrdCheck_ok :
    wordLin (hnRhoT ++ hnCAlpha) = wordLin (hnCAlpha ++ hnWAlpha) ∧
      wordLin (hnRhoT ++ hnCBeta) = wordLin (hnCBeta ++ hnWBeta) ∧ wordLin hnWAB5 = 1 :=
  Certificates.certificate6073

end CFSG.Monster.Existence
