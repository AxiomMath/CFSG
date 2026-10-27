module

public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.He.Simple
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

namespace Insp7

theorem card_carrier_big
    {s : TauCeti.SporadicName}
    (hs : s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) :
    2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · show 2 ^ 9 ∣ Nat.card NativeSporadic.M24
    rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num
  · show 2 ^ 9 ∣ Nat.card NativeSporadic.J4
    rw [CFSG.Sporadic.J4.card_J4]; norm_num
  · show 2 ^ 9 ∣ Nat.card NativeSporadic.HS
    rw [CFSG.Sporadic.HS.card_HS]; norm_num
  · show 2 ^ 9 ∣ Nat.card NativeSporadic.He
    rw [CFSG.Sporadic.He.card_He]; norm_num
  · show 2 ^ 9 ∣ Nat.card NativeSporadic.Ru
    rw [CFSG.Sporadic.Ru.card_Ru]; norm_num

end Insp7

end CFSG.Quasithin
