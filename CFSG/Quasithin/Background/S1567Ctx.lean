module

public import CFSG.Quasithin.Background.C1PackS15367

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

structure Ctx67 (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t : G) : Prop where
  c : Ctx153 G T Mc M V₁ V₂ t
  r45 : Res15345 T Mc M V₁ V₂
  r46 : Res15346 T M V₁ V₂
  r49 : Res15349 T Mc M V₁
  r50 : Res15350 T M
  L : LineData153 T M V₁ V₂ E
  r66 : Res15366B T Mc M V₁ V₂ E
  r2 : Res15367Two T M E

@[expose] def Step67Normal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t : G),
    Ctx67 G T Mc M V₁ V₂ E t →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (YE153 Mc M E : Set G)

@[expose] def Step67Index : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t : G),
    Ctx67 G T Mc M V₁ V₂ E t →
      (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3

end CFSG.Quasithin
