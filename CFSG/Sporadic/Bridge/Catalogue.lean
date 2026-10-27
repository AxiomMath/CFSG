module

public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.J1
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.Bridge.M23Surj
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Sporadic.Bridge.Y322Central
public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.Sporadic.Bridge.Co1Surj
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Bridge.M24Surj
public import CFSG.Sporadic.Bridge.Fi24Surj
public import CFSG.Sporadic.Bridge.LySurj
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.Sporadic.Presentation.Co2Exact
public import CFSG.Sporadic.Bridge.Fi22Surj
public import CFSG.Sporadic.Bridge.BBound
public import CFSG.Sporadic.Presentation.McLExact

public section

namespace CFSG.Sporadic.Bridge

theorem sporadicRep_iff_tauCeti (G : Type) [Group G] :
    Models.SporadicRep G ↔ ∃ s : TauCeti.SporadicName, Nonempty (G ≃* s.Group) := Iff.rfl

theorem nonempty_carrier_mulEquiv_group
    (s : TauCeti.SporadicName) :
    Nonempty (Blueprint.NativeSporadic.Carrier s ≃* s.Group) := by
  cases s
  case M11 => exact M11.nonempty_mulEquiv
  case M12 => exact M12.nonempty_mulEquiv
  case M22 => exact M22.nonempty_mulEquiv
  case J1 => exact J1.nonempty_mulEquiv
  case J2 => exact J2.nonempty_mulEquiv
  case ONan => exact ON.nonempty_mulEquiv
  case M23 => exact M23.nonempty_mulEquiv
  case Fi23 => exact Fi23.nonempty_mulEquiv
  case Co3 => exact Co3.nonempty_mulEquiv
  case HN => exact HN.nonempty_mulEquiv
  case J3 => exact J3.nonempty_mulEquiv
  case Suz => exact Suz.nonempty_mulEquiv
  case Co1 => exact Co1.nonempty_mulEquiv
  case HS => exact HS.nonempty_mulEquiv
  case M24 => exact M24.nonempty_mulEquiv
  case Fi24Prime => exact Fi24.nonempty_mulEquiv
  case Ly => exact Ly.nonempty_mulEquiv
  case He => exact He.nonempty_mulEquiv
  case Th => exact Th.nonempty_mulEquiv
  case J4 => exact J4.nonempty_mulEquiv
  case McL => exact McL.nonempty_mulEquiv
  case Ru => exact Ru.nonempty_mulEquiv
  case Co2 => exact Co2.nonempty_mulEquiv
  case Fi22 => exact Fi22.nonempty_mulEquiv
  case B => exact B.nonempty_mulEquiv
  case M => exact Y443.nonempty_mulEquiv

end CFSG.Sporadic.Bridge
