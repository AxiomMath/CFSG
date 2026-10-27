module

public import Certificates.Certificate6075

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels)

theorem hnRelsCheck_ok_0 :
    ∀ i ∈ [4, 5, 6, 7, 10, 11, 12], wordLin (hnRelW hnRels[i]!) = 1 :=
  Certificates.certificate6075

end CFSG.Monster.Existence
