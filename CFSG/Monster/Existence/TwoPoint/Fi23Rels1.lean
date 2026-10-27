
module


public import Certificates.Certificate6050

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

theorem fiRelsCheck_ok_1 :
    ∀ i ∈ [4, 11, 14, 22, 29, 35, 38, 45, 53], wordLin (fiRelW rels[i]!) = 1 :=
  Certificates.certificate6050

end CFSG.Monster.Existence
