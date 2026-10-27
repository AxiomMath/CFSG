
module


public import Certificates.Certificate6051

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

theorem fiRelsCheck_ok_2 :
    ∀ i ∈ [5, 13, 24, 27, 31, 37, 39, 40, 49], wordLin (fiRelW rels[i]!) = 1 :=
  Certificates.certificate6051

end CFSG.Monster.Existence
