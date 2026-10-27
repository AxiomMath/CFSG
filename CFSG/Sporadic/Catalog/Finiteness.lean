module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Catalog

open CFSG.Blueprint.NativeSporadic

theorem finite_carrier_of_ne_M (s : TauCeti.SporadicName) (hs : s ≠ .M) : Finite (Carrier s) := by
  cases s <;> first | exact absurd rfl hs | (dsimp only [Carrier]; infer_instance)

end CFSG.Sporadic.Catalog
