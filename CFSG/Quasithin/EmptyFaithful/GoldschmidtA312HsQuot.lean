
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsKInputs
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSQuot.Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSBase

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS

public section

namespace CFSG.Quasithin.A312Hs

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.Sporadic.HS.Native (hsData)

theorem hs_Y2_quot
    (N : Subgroup (hsCtx.Y 2)) [N.Normal] (hp : IsPGroup 2 (hsCtx.Y 2 ⧸ N)) :
    Nat.card (hsCtx.Y 2 ⧸ N) ≤ 1 :=
  (Certificates.certificate4102.2.2.2.1).2.2 N hp

end CFSG.Quasithin.A312Hs
