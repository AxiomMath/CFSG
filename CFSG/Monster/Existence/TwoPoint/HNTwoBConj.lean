module

public import Certificates.Certificate6079

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem hnTwoBCheck_ok :
    wordLin (hnXWord ++ hnCW) = wordLin (hnCW ++ hnWW) :=
  Certificates.certificate6079

end CFSG.Monster.Existence
