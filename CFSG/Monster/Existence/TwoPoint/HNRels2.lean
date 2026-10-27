module

public import Certificates.Certificate6077

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels)

theorem hnRelsCheck_ok_2 :
    ∀ i ∈ [13, 14, 15], wordLin (hnRelW hnRels[i]!) = 1 :=
  Certificates.certificate6077

end CFSG.Monster.Existence
