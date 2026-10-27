module

public import CFSG.Quasithin.Background.F6Solvable
public import CFSG.Quasithin.Background.E2Seventeen

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open

@[expose] def Input15111YCoreFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I P H V D : Subgroup G) (c : G),
    F6.IsGoldschmidtTripleIn I P H → pCoreOf 2 I = ⊥ → V ≤ P →
    P ≤ Subgroup.normalizer (V : Set G) → Nat.card V = 16 → IsElemAbelian 2 V →
    ¬ V ≤ pCoreOf 2 H → c ∈ P → c ^ 3 = 1 → (∀ v ∈ V, c * v * c⁻¹ = v → v = 1) →
    D ≤ H → H ≤ Subgroup.normalizer (D : Set G) → E2.IsExtraspecialPlus 2 D → False

end Y15111

end CFSG.Quasithin
