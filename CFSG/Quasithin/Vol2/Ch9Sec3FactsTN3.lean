module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsTNR
public import CFSG.Quasithin.Vol2.Ch9Sec3TNU35

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

@[expose] def A314ThreeNormRest3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SQTKHyp Y → CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2 →
    ∀ T B L D : Subgroup Y,
    IsSylowTwoOf T ⊤ → B ∈ lFamily T → IsAlt 5 (ModO2 B) → L ∈ cComp ⊤ → B < L →
    A314Statement T B L → L.Normal → IsPGroup 3 D → (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) →
    (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y) → ¬ D ≤ L →
    (∃ b ∈ B ⊓ D, orderOf b = 3 ∧ b ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Y) : Set Y)) →
    T ≤ Subgroup.normalizer (B : Set Y) → (∀ x ∈ D, x ^ 3 = 1) →
    ((IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L))) →
      D ≤ Subgroup.normalizer (B : Set Y)

theorem a314ThreeNormRest2_of (h : A314ThreeNormRest3) :
    A314ThreeNormRest2 := by
  intro Y _ _ hY h3 T B L D hT hB hA5 hL hBL h314 hLn hD3 hDab hDT hDL hb hTB hD3e hrest
  rcases hrest with h4 | h1314
  · exact TN.le_normalizer_of_four_minus h3 hT hA5 hBL.le hLn h4 hD3 hDab hDT hDL hb hTB hD3e
  · exact h Y hY h3 T B L D hT hB hA5 hL hBL h314 hLn hD3 hDab hDT hDL hb hTB hD3e h1314

end CFSG.Quasithin.H13.Ch9
