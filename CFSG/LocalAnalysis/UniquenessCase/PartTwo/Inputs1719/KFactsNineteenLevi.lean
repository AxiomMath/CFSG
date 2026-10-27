module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def IsDynkinFamilyIn (M Dsub : Subgroup G) (d : ℕ) (K J : Fin d → Subgroup G) :
    Prop :=
  let O := pCoreOf 2 (Dsub ⊓ M)
  (∀ i, O ≤ K i ∧ K i ≤ Dsub ⊓ M ∧ ((K i).subgroupOf (Dsub ⊓ M)).Normal ∧
      K i = Opp 2 (K i) ⊔ O ∧ ¬ J i ≤ O) ∧
    (∀ i j : Fin d, i ≠ j → ⁅K i, K j⁆ ≤ O) ∧
    (⨆ i, K i) = Opp 2 (Dsub ⊓ M) ⊔ O ∧
    (∀ (i : Fin d) (A B : Subgroup G), O ≤ A → O ≤ B → A = Opp 2 A ⊔ O →
      B = Opp 2 B ⊔ O → A ⊔ B = K i → ⁅A, B⁆ ≤ O → A = K i ∨ B = K i) ∧
    (∀ i, J i = S17.oUpperTwo (K i))

theorem isDynkinComponentFamily_iff (D : Data G) (Dsub : Subgroup G) (d : ℕ)
    (K J : Fin d → Subgroup G) :
    IsDynkinComponentFamily D Dsub d K J ↔ IsDynkinFamilyIn D.M Dsub d K J := Iff.rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

@[expose] def K_19_18_levi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Dsub : Subgroup G),
    CFSG.Open.IsQuasisimple (Bar2 Dsub) →
    List19_16_5 (BarInf Dsub) →
    IsNontrivialParabolic (Bar2 Dsub) (barOfInter M Dsub) →
    pCoreOf 2 Dsub ≤ M →
    ∃ (d : ℕ) (K J : Fin d → Subgroup G), IsDynkinFamilyIn M Dsub d K J ∧
      ∀ X : Subgroup G, X ≤ normalizer (Opp 2 (Dsub ⊓ M) : Set G) →
        ¬ ⁅Opp 2 (Dsub ⊓ M), X⁆ ≤ pCoreOf 2 (Opp 2 (Dsub ⊓ M)) →
          ∃ i : Fin d, J i ≤ ⁅Opp 2 (Dsub ⊓ M), X⁆

@[expose] def K_19_21_levi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Dsub : Subgroup G),
    CFSG.Open.IsQuasisimple (Bar2 Dsub) →
    List19_16_5 (BarInf Dsub) →
    IsNontrivialParabolic (Bar2 Dsub) (barOfInter M Dsub) →
    pCoreOf 2 Dsub ≤ M →
    ∀ (d : ℕ) (K J : Fin d → Subgroup G), IsDynkinFamilyIn M Dsub d K J →
    ∀ (i : Fin d) (n : ℕ), 3 ≤ n → IsL2 (Bar2 (J i)) n →
      d ≤ 2 ∧
      (∀ k, ⁅J k, J k⁆ = J k ∧ CFSG.Open.IsQuasisimple (Bar2 (J k)) ∧
        K k = J k ⊔ pCoreOf 2 (Dsub ⊓ M)) ∧
      (∀ g ∈ normalizer ((Dsub ⊓ M : Subgroup G) : Set G), Odd (orderOf g) →
        ∀ k, g ∈ normalizer ((K k : Subgroup G) : Set G))

@[expose] def K_L2_oddAbelianBorel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J B : Subgroup G) (n : ℕ),
    IsL2 (Bar2 J) n → B ≤ normalizer (J : Set G) → IsMulCommutative ↥B → Odd (Nat.card B) →
    (∀ b ∈ B, b ^ (2 ^ n - 1) = 1) →
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S J ∧ B ≤ normalizer (S : Set G)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
