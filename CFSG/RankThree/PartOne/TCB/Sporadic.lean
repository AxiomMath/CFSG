module

public import CFSG.RankThree.PartOne.TCB.BabyRoute
public import CFSG.Sporadic.Bridge.Co1Surj
public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Sporadic.Bridge.Fi22Surj
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Sporadic.Bridge.Fi24Surj
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.Bridge.J1
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.Sporadic.Bridge.LySurj
public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Bridge.M23Surj
public import CFSG.Sporadic.Bridge.M24Surj
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Sporadic.Bridge.Y322Central
public import CFSG.Sporadic.Presentation.Co2Exact
public import CFSG.Sporadic.Presentation.McLExact

public section

namespace CFSG.RankThree.PartOne.TCB

open TauCeti

theorem nonempty_carrier_mulEquiv_group
    (s : SporadicName) : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* s.Group) := by
  cases s
  case M11 => exact CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  case M12 => exact CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  case M22 => exact CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  case J1 => exact CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  case J2 => exact CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  case ONan => exact CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  case M23 => exact CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  case Fi23 => exact CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
  case Co3 => exact CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  case HN => exact CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  case J3 => exact CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  case Suz => exact CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  case Co1 => exact CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  case HS => exact CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  case M24 => exact CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  case Fi24Prime => exact CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  case Ly => exact CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  case He => exact CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  case Th => exact CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  case J4 => exact CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  case McL => exact CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  case Ru => exact CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  case Co2 => exact CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  case Fi22 => exact CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  case B => exact nonempty_mulEquiv_B
  case M => exact CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv

end CFSG.RankThree.PartOne.TCB
