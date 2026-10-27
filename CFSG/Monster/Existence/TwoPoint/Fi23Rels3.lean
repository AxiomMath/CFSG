
module


public import Certificates.Certificate6052

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

theorem fiRelsCheck_ok_3 :
    ∀ i ∈ [1, 3, 16, 20, 28, 32, 46, 51], wordLin (fiRelW rels[i]!) = 1 :=
  Certificates.certificate6052

end CFSG.Monster.Existence
