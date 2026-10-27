
module


public import Certificates.Certificate6061

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem s4PowCheck_ok :
    wordLin (s4WGamma ++ s4WGamma) = 1 ∧ wordLin (fiWU[8]! ++ fiWU[8]!) = 1 ∧
      wordLin (s4WGamma ++ fiWBeta) = wordLin (fiWBeta ++ s4WGamma) ∧
      wordLin (s4WE8Gamma ++ s4WE8Gamma ++ s4WE8Gamma) = 1 ∧
      wordLin (s4WAlphaGamma ++ s4WAlphaGamma ++ s4WAlphaGamma) = 1 ∧
      wordLin s4WE8Gamma ≠ 1 ∧ wordLin s4WAlphaGamma ≠ 1 :=
  Certificates.certificate6061

end CFSG.Monster.Existence
