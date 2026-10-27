module

public import Certificates.Certificate6072

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

theorem gxTwoBCheck_ok :
    wordLin (gxXWord ++ gxCW9) = wordLin (gxCW9 ++ gxProdWord (gxXList 9)) :=
  Certificates.certificate6072

end CFSG.Monster.Existence
