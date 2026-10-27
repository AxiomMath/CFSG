
module


public import Certificates.Certificate6053

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

theorem fiRelsCheck_ok_4 :
    ∀ i ∈ [10, 12, 15, 25, 33, 34, 36, 42, 50, 54], wordLin (fiRelW rels[i]!) = 1 :=
  Certificates.certificate6053

end CFSG.Monster.Existence
