module

public import Certificates.Certificate6076

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels)

theorem hnRelsCheck_ok_1 :
    ∀ i ∈ [0, 1, 2, 3, 8, 9], wordLin (hnRelW hnRels[i]!) = 1 :=
  Certificates.certificate6076

end CFSG.Monster.Existence
