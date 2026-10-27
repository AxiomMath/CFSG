module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

@[expose] def K_19_11_torusFixed : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n p : ℕ), p.Prime →
    ((IsSp4 X n ∧ Odd n ∧ 1 < n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      ((IsL2Square X n ∨ (S17.IsL2U3Product X n ∧ IsPowTwo n)) ∧ 2 < n ∧
        (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSzSquare X n ∧ 2 < n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) →
    ∀ (A : Subgroup X) (t : X), IsZModSq ↥A n → (∃ k : ℕ, orderOf t = 2 ^ k) →
      (∀ a ∈ A, t * a * t⁻¹ = a⁻¹) →
    ∀ Q : Subgroup (MulAut X), IsPGroup 2 Q →
      (∀ b ∈ A ⊔ zpowers t, MulAut.conj b ∈ normalizer (Q : Set (MulAut X))) →
      ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        ∀ α ∈ Q, ∀ e ∈ E, α e = e

@[expose] def K_19_21_BN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Dsub A E : Subgroup G) (r : ℕ),
    CFSG.Open.IsQuasisimple (Bar2 Dsub) →
    List19_16_5 (BarInf Dsub) →
    IsNontrivialParabolic (Bar2 Dsub) (barOfInter M Dsub) →
    pCoreOf 2 Dsub ≤ M → A ≤ M → A ≤ normalizer (Dsub : Set G) →
    IsMulCommutative ↥A → Odd (Nat.card A) →
    (∃ P₀ : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 P₀ (Dsub ⊓ M) ∧
      A ≤ normalizer (P₀ : Set G)) →
    r.Prime → E ≤ A → IsPGroup r E →
    ∃ R P : Subgroup G, IsPGroup r R ∧ E ≤ R ∧ R ≤ M ∧
      CFSG.ABGLocalTools.IsSylowOf 2 P (Dsub ⊓ M) ∧
      Dsub ≤ P ⊔ (Dsub ⊓ normalizer (R : Set G))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
