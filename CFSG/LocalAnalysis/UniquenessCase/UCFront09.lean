module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Inv9 (K X : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {R | R ≤ K ∧ IsPGroup p ↥R ∧ X ≤ normalizer (R : Set G)}

@[expose] def Inv9' (K X : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {R | R ≤ K ∧ ¬ p ∣ Nat.card R ∧ X ≤ normalizer (R : Set G)}

@[expose] def Thin9 (L : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p L ≤ 1

@[expose] def calY9 (D : Data G) : Set (Subgroup G) :=
  {Y | Y ≤ D.M ∧ calNOf Y ≠ {D.M} ∧
    ∀ A : Subgroup G, A ≤ Y → Nat.card A = 3 → A ∈ uniqueSet D.M}

@[expose] def calH9 (D : Data G) (Y : Subgroup G) : Set (Subgroup G) :=
  {H | Y ≤ H ∧ ¬ H ≤ D.M ∧
    CFSG.Open.pRank 3 (⨆ h : ↥H, (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom : Subgroup G) = 1}

@[expose] def calY2_9 (D : Data G) : Set (Subgroup G) :=
  {Y | Y ∈ calY9 D ∧ calMOf Y ≠ {D.M} ∧ calMOf Y ⊆ calH9 D Y ∪ {D.M} ∧
    (∀ A ∈ Inv9' D.M Y 3, ⁅A, Opp 3 Y⁆ ≤ pCoreOf 2 A) ∧
    ∃ k : ℕ, ((Opp 3 Y).subgroupOf Y).index = 2 ^ k}

@[expose] def calY2Star9 (D : Data G) : Set (Subgroup G) :=
  {Y | Maximal (· ∈ calY2_9 D) Y}

@[expose] def calH2_9 (D : Data G) (Y : Subgroup G) : Set (Subgroup G) :=
  {H | H ∈ calH9 D Y ∧ Fstar H = pCoreOf 2 H}

@[expose] def Hyp91 (D : Data G) (Y H D₃ : Subgroup G) : Prop :=
  Y ∈ calY9 D ∧ H ∈ calH9 D Y ∧ D₃ ≤ Opp 3 Y ∧ Nat.card D₃ = 3

@[expose] def Hyp97 (D : Data G) (Y H D₃ S : Subgroup G) : Prop :=
  Hyp91 D Y H D₃ ∧ Y ∈ calY2Star9 D ∧ H ∈ calH2_9 D Y ∧ CFSG.ABGLocalTools.IsSylowOf 2 S Y

@[expose] def R923 (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, L ≤ D.M → D.M ≤ normalizer (L : Set G) → IsAlt (Bar2 L) 5 →
    UniqueMax D.M (L ⊔ D.T) →
    (∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P L → P ∈ uniqueSet D.M) →
    ∀ X : Subgroup G, Opp 3 X = X → X ≤ L → L = X ⊔ pCoreOf 2 L →
      ⁅pCoreOf 2 D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ⊓ X, X⁆ ≠ ⊥ →
        calNOf X = {D.M}

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
