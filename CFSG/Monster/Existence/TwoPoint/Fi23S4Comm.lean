
module


public import Certificates.Certificate6059

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem s4CommGenCheck_ok :
    ∀ i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 9],
      wordLin (s4WGamma ++ fiWU[i]!) = wordLin (fiWU[i]! ++ s4WGamma) :=
  Certificates.certificate6059

end CFSG.Monster.Existence
