module

public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin.MS93

variable {G : Type*} [Group G]

@[expose] def C134SqCond (R L : Subgroup G) : Prop :=
  ∀ T₁ : Subgroup G, T₁ ≤ R → (T₁.subgroupOf R).Characteristic →
    Nat.card ↥(omegaOneCenterOf T₁ ⊓ Subgroup.centralizer (L : Set G)) ^ 2 ≤
      Nat.card ↥(omegaOneCenterOf T₁)

end CFSG.Quasithin.MS93
