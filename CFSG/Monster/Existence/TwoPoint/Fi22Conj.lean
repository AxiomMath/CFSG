module

public import Certificates.Certificate6046

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem fi22Check_ok :
    (wordLin (fiRhoT ++ fiCGamma) = wordLin (fiCGamma ++ fiWU[0]!) ∧
        wordLin (fiRhoT ++ fiCDelta) = wordLin (fiCDelta ++ fiWDelta)) ∧
      fiImgConjCheck 0 27 = true :=
  Certificates.certificate6046

end CFSG.Monster.Existence
