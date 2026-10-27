
module


public import Certificates.Certificate6047

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem fiConjCheck_ok :
    wordLin (fiRhoT ++ fiCAlpha) = wordLin (fiCAlpha ++ fiWAlpha) ∧
      wordLin (fiWAB ++ fiCThreeA) = wordLin (fiCThreeA ++ wordThreeA) :=
  Certificates.certificate6047

end CFSG.Monster.Existence
