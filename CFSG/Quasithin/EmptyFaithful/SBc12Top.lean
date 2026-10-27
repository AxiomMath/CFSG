module

public import CFSG.Quasithin.Background.E2Seventeen
public import CFSG.Quasithin.EmptyFaithful.S151Statements

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBc12

@[expose] def Input15111Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → ∀ H : Subgroup G, IsHStar T M H →
      ¬ V154 T Mc M ≤ pCoreOf 2 H →
      (∃ D : Subgroup G, D ≤ conjClosure (V154 T Mc M) H ∧
        conjClosure (V154 T Mc M) H ≤ Subgroup.normalizer (D : Set G) ∧ E2.IsExtraspecialPlus 2 D ∧
        ∃ φ : ↥(conjClosure (V154 T Mc M) H) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
          φ.ker = D.subgroupOf (conjClosure (V154 T Mc M) H)) → False

variable {G : Type} [Group G] [Finite G] {T Mc M H : Subgroup G}

end SBc12

end CFSG.Quasithin
