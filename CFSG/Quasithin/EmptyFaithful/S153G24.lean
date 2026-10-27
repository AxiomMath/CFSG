module

public import CFSG.Quasithin.EmptyFaithful.S153DInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def L4Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L → IsLnTwoQuot L 4 →
      (IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
        Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) ∧
      L ≤ Subgroup.centralizer (V₁ : Set G)

end CFSG.Quasithin
