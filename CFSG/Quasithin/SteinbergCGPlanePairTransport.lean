module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSetting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer4

public section

namespace CFSG.Quasithin.SteinbergCG

open Subgroup CFSG CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Thompson

variable {G : Type*} [Group G] [Finite G] {H T : Subgroup G}

theorem thompsonJ_subgroupOf_map (hTH : T ≤ H) :
    (thompsonJ (T.subgroupOf H)).map H.subtype = thompsonJ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Wreath.elemThompsonIn_two_eq, ← Wreath.elemThompsonIn_two_eq,
    ← elemThompsonIn_map_of_injective 2 H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hTH]

end Thompson

end CFSG.Quasithin.SteinbergCG
