module

public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Input15120J4Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    IsSporadic .J4 (↥L ⧸ CFSG.pCore 2 ↥L) →
    ∃ K : Subgroup G, K ∈ lFamilyOf (g1_1516 Z₁) (s1516 T Z₁) ∧ CharTwo K ∧
      IsSporadic .M24 (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      K ⊔ (L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G)) = L

end CFSG.Quasithin
