module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsTN
public import CFSG.Quasithin.Vol2.Ch9Sec3TNInner
public import CFSG.Quasithin.Vol2.Ch9Sec3TNSpor

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

@[expose] def A314ThreeNormRest2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SQTKHyp Y → CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2 →
    ∀ T B L D : Subgroup Y,
    IsSylowTwoOf T ⊤ → B ∈ lFamily T → IsAlt 5 (ModO2 B) → L ∈ cComp ⊤ → B < L →
    A314Statement T B L → L.Normal → IsPGroup 3 D → (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) →
    (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y) → ¬ D ≤ L →
    (∃ b ∈ B ⊓ D, orderOf b = 3 ∧ b ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Y) : Set Y)) →
    T ≤ Subgroup.normalizer (B : Set Y) → (∀ x ∈ D, x ^ 3 = 1) →
    ((IsSL2 5 ↥B ∧ (IsPSLEps3 false 5 1 ↥L ∨ IsSLEps3 false 5 ↥L) ∧
        B = perfectCore (L ⊓ Subgroup.centralizer (pCoreOf 2 B : Set Y))) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L))) →
      D ≤ Subgroup.normalizer (B : Set Y)


theorem a314ThreeNormRest_of (h : A314ThreeNormRest2) : A314ThreeNormRest := by
  intro Y _ _ hY h3 T B L D hT hB hA5 hL hBL h314 hLn hD3 hDab hDT hDL hb hTB hD3e hLie
  rcases TN.center_or_inner_of_a314 (perfect_of_mem_cComp hL) h314 hLie with hcase | hrest
  · obtain ⟨b, ⟨hbB, hbD⟩, hb3, -⟩ := hb
    have hb1 : b ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hb3
      omega
    exact TN.le_normalizer_of_center_or_inner h3 hLn hBL.le hcase hD3 hDab hD3e hDL hbB hbD hb1
      (TN.exists_not_commute_of_a5 hBL.le hA5 hbB hb3)
  · exact h Y hY h3 T B L D hT hB hA5 hL hBL h314 hLn hD3 hDab hDT hDL hb hTB hD3e hrest

end CFSG.Quasithin.H13.Ch9
