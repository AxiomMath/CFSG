module

public import CFSG.Quasithin.EmptyFaithful.ModDGlue

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.facts14610_G22_of_sylow
    {H : Subgroup G} {u : G}
    {I I₂ K : Subgroup G} (c : Facts14610 T M H u I I₂) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hK : Concl14610List T M I I₂ K) (hG2 : IsG2Block K) :
    Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3 :=
  le_antisymm (ModD.g22_bound c hK hsyl hLT hG2)
    (Setting146.eight_le_card_conjClosure_I₂ c.toHyp14610)

end CFSG.Quasithin
