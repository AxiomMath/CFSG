module

public import CFSG.RankThree.GF2n.Item310
import CFSG.Sporadic.Bridge.M23Surj
import CFSG.Sporadic.Bridge.M24Surj
import CFSG.Sporadic.Bridge.J3Surj
import CFSG.Sporadic.Bridge.J4Surj
import CFSG.Sporadic.Bridge.Co1Surj
import CFSG.Sporadic.Presentation.Co2Exact
import CFSG.Sporadic.Bridge.HSSurj
import CFSG.Sporadic.Bridge.SuzSurj
import CFSG.Sporadic.Bridge.HeSurj
import CFSG.Sporadic.Bridge.Fi24Surj
import CFSG.Sporadic.Bridge.HNSurj
import CFSG.Sporadic.Bridge.ThSurj
import CFSG.Sporadic.Bridge.BBound
import CFSG.Sporadic.Bridge.Y322Central

public section

namespace CFSG.RankThree.GF2n

theorem sporadicBridge_M23 :
    SporadicBridge .M23 :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv

theorem sporadicBridge_M24 :
    SporadicBridge .M24 :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv

theorem sporadicBridge_J3 :
    SporadicBridge .J3 :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv

theorem sporadicBridge_J4 :
    SporadicBridge .J4 :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv

theorem sporadicBridge_Co1 :
    SporadicBridge .Co1 :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv

theorem sporadicBridge_Co2 :
    SporadicBridge .Co2 :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv

theorem sporadicBridge_HS :
    SporadicBridge .HS :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv

theorem sporadicBridge_Suz :
    SporadicBridge .Suz :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv

theorem sporadicBridge_He :
    SporadicBridge .He :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.He.nonempty_mulEquiv

theorem sporadicBridge_Fi24Prime :
    SporadicBridge .Fi24Prime :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv

theorem sporadicBridge_HN :
    SporadicBridge .HN :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv

theorem sporadicBridge_Th :
    SporadicBridge .Th :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv

theorem sporadicBridge_B
    : SporadicBridge .B :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.B.nonempty_mulEquiv

theorem sporadicBridge_M :
    SporadicBridge .M :=
  sporadicBridge_of_nonempty CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv

end CFSG.RankThree.GF2n
