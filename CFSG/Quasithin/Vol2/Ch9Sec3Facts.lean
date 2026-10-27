module

public import CFSG.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

@[expose] def A314ThreeNormFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SQTKHyp Y → CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2 →
    ∀ T B L D : Subgroup Y,
    IsSylowTwoOf T ⊤ → B ∈ lFamily T → IsAlt 5 (ModO2 B) → L ∈ cComp ⊤ → B < L →
    A314Statement T B L → L.Normal → IsPGroup 3 D → (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) →
    (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y) → ¬ D ≤ L →
    (∃ b ∈ B ⊓ D, orderOf b = 3 ∧ b ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Y) : Set Y)) →
    T ≤ Subgroup.normalizer (B : Set Y) → (∀ x ∈ D, x ^ 3 = 1) →
      D ≤ Subgroup.normalizer (B : Set Y)

end CFSG.Quasithin.H13.Ch9
