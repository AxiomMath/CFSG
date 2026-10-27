module

public import CFSG.Quasithin.Vol2.Ch9Sec3Facts
public import CFSG.Quasithin.Vol2.Ch9Sec3TNLie

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

@[expose] def A314ThreeNormRest : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SQTKHyp Y → CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2 →
    ∀ T B L D : Subgroup Y,
    IsSylowTwoOf T ⊤ → B ∈ lFamily T → IsAlt 5 (ModO2 B) → L ∈ cComp ⊤ → B < L →
    A314Statement T B L → L.Normal → IsPGroup 3 D → (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) →
    (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y) → ¬ D ≤ L →
    (∃ b ∈ B ⊓ D, orderOf b = 3 ∧ b ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Y) : Set Y)) →
    T ≤ Subgroup.normalizer (B : Set Y) → (∀ x ∈ D, x ^ 3 = 1) →
    ¬ (IsPSL 3 2 2 ↥L ∨ IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L ∨ Is3D4 2 2 ↥L) →
      D ≤ Subgroup.normalizer (B : Set Y)


theorem a314ThreeNormFact_of (h : A314ThreeNormRest) : A314ThreeNormFact := by
  intro Y _ _ hY h3 T B L D hT hB hA5 hL hBL h314 hLn hD3 hDab hDT hDL hb hTB hD3e
  by_cases hLie : IsPSL 3 2 2 ↥L ∨ IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L ∨ Is3D4 2 2 ↥L
  · exact TN.le_normalizer_of_three_lie hT hB hL hBL hLn hLie hD3 hDT hTB
  · exact h Y hY h3 T B L D hT hB hA5 hL hBL h314 hLn hD3 hDab hDT hDL hb hTB hD3e hLie

end CFSG.Quasithin.H13.Ch9
