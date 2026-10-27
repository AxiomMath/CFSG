module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223P4

namespace B

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem not_A6_G2 (kP : Input21ProperRank) (c : P4Ctx T Mc M H B₀ I X)
    (f : P4Fact T Mc M H B₀ I X) (hb : IsAltBlockType X 6 ∨ IsG2Block X) : False := by
  have h1 := kP G X (sOf152 T Mc M B₀ ⊓ X) (oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X)) hb f.sylow
    le_sup_right (Y_le_X f) (Y_ne_X c f)
  have h2 := f.rank_Y
  omega

end B

end S15223P4

end CFSG.Quasithin
