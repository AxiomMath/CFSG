
module


public import Certificates.Certificate6049

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

theorem fiRelsCheck_ok_0 :
    ∀ i ∈ [0, 7, 9, 17, 21, 26, 41, 47, 48, 52], wordLin (fiRelW rels[i]!) = 1 :=
  Certificates.certificate6049

end CFSG.Monster.Existence
