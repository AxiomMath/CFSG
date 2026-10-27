module

public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Bridge.J1
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Presentation.M23
public import CFSG.Sporadic.Presentation.M24
public import CFSG.Sporadic.Presentation.J3
public import CFSG.Sporadic.Presentation.HS
public import CFSG.Sporadic.Presentation.McL
public import CFSG.Sporadic.Presentation.He
public import CFSG.Sporadic.Presentation.Ru
public import CFSG.Sporadic.Presentation.Suz
public import CFSG.Sporadic.Presentation.ONan
public import CFSG.Sporadic.Presentation.Co1
public import CFSG.Sporadic.Presentation.Co2
public import CFSG.Sporadic.Presentation.Co3
public import CFSG.Sporadic.Presentation.Fi22
public import CFSG.Sporadic.Presentation.Fi23
public import CFSG.Sporadic.Presentation.Fi24Prime
public import CFSG.Sporadic.Presentation.HN
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Presentation.Th
public import CFSG.Sporadic.Presentation.J4
public import CFSG.Sporadic.Presentation.B
public import CFSG.Sporadic.NativeFinite

public section

namespace CFSG.Sporadic.Presentation

open TauCeti

theorem finite_of_bridge (s : SporadicName) (hs : s ≠ .M)
    (h : Nonempty (Blueprint.NativeSporadic.Carrier s ≃* s.Group)) : Finite s.Group := by
  obtain ⟨e⟩ := h
  have := finite_carrier_of_ne_M s hs
  exact Finite.of_equiv _ e.toEquiv

theorem finite_group_of
    (hM : Finite SporadicName.M.Group) (s : SporadicName) :
    Finite s.Group := by
  cases s with
  | M11 => exact finite_of_bridge .M11 (by decide) Bridge.M11.nonempty_mulEquiv
  | M12 => exact finite_of_bridge .M12 (by decide) Bridge.M12.nonempty_mulEquiv
  | M22 => exact finite_of_bridge .M22 (by decide) Bridge.M22.nonempty_mulEquiv
  | M23 => exact M23.finite_card_le.1
  | M24 => exact M24.finite
  | J1 => exact finite_of_bridge .J1 (by decide) Bridge.J1.nonempty_mulEquiv
  | J2 => exact finite_of_bridge .J2 (by decide) Bridge.J2.nonempty_mulEquiv
  | J3 => exact J3.finite_card_le.1
  | J4 => exact J4.finite_card_le.1
  | HS => exact HS.finite
  | McL => exact McL.finite
  | He => exact He.finite
  | Ru => exact Ru.finite
  | Suz => exact Suz.finite_card_le.1
  | ONan => exact ONan.finite_card_le.1
  | Co1 => exact Co1.finite_card_le.1
  | Co2 => exact Co2.finite
  | Co3 => exact Co3.finite_card_le.1
  | Fi22 => exact Fi22.finite
  | Fi23 => exact Fi23.finite_card_le.1
  | Fi24Prime => exact Fi24Prime.finite_card_le.1
  | HN => exact HN.finite_card_le.1
  | Ly => exact Ly.finite_card_le.1
  | Th => exact Th.finite_card_le.1
  | B => exact B.finite_card_le.1
  | M => exact hM

end CFSG.Sporadic.Presentation
