
module


public import Certificates.Certificate6060

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem s4ConjCheck_ok :
    wordLin (fiRhoT ++ s4CGamma) = wordLin (s4CGamma ++ s4WGamma) ∧
      wordLin (fiRhoT ++ s4CBetaGamma) = wordLin (s4CBetaGamma ++ s4WBetaGamma) :=
  Certificates.certificate6060

end CFSG.Monster.Existence
