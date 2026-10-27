module

public import Certificates.Certificate6078

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels)

theorem hnRelsCheck_ok_3 :
    ∀ i ∈ [16, 17, 18], wordLin (hnRelW hnRels[i]!) = 1 :=
  Certificates.certificate6078

end CFSG.Monster.Existence
