
module


public import Certificates.Certificate6054

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

theorem fiRelsCheck_ok_5 :
    ∀ i ∈ [2, 6, 8, 18, 19, 23, 30, 43, 44], wordLin (fiRelW rels[i]!) = 1 :=
  Certificates.certificate6054

end CFSG.Monster.Existence
