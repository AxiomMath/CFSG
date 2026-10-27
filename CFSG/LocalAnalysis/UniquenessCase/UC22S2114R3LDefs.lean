module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_14R3LF (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ∀ f : ℕ, (LieModel (BarInf L) .PSL 4 2 f ∨ LieModel (BarInf L) .PSp 3 2 f ∨
      IsOmega8m (BarInf L) f) →
    (∀ r : ℕ, r.Prime → r ∣ 2 ^ c.n - 1 → r ∣ f) →
    D.k = 1 → Odd c.n → 3 ≤ c.n → c.B0 ≤ normalizer (D.T : Set G) →
    c.B0 ≤ normalizer (L : Set G) → (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_14R3LT (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ∀ f : ℕ, (LieModel (BarInf L) .PSL 4 2 f ∨ LieModel (BarInf L) .PSp 3 2 f ∨
      IsOmega8m (BarInf L) f) →
    D.k = 1 → Odd c.n → 3 ≤ c.n → c.B0 ≤ normalizer (D.T : Set G) →
    c.B0 ≤ normalizer (L : Set G) → (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    D.M ≤ normalizer (L : Set G) →
    ∀ r : ℕ, r.Prime → 7 ≤ r → r ∣ 2 ^ c.n - 1 → r ∣ 2 ^ f - 1 → ¬ r ∣ f → r ∉ D.sig →
    (∀ p ∈ D.sig, ∀ E : Subgroup G, E ≤ L → IsElemAbelian r E → Nat.card E = r ^ 2 →
      CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) ≤ 1) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_14R3LK2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ∀ f : ℕ, Odd f → 3 ≤ f → LieModel (BarInf L) .PSL 4 2 f → D.k = 2 → 3 ≤ c.n →
    c.B0 ≤ normalizer (L : Set G) → (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    D.M ≤ normalizer (L : Set G) → CFSG.Open.pRank 3 D.M ≤ 3 → 3 ∉ D.sig →
    (∀ p ∈ D.sig, ∀ R E : Subgroup G, IsSylowOf 3 R D.M → E ≤ R ⊓ centralizer (R : Set G) →
      IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
        CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) ≤ 1) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

end CFSG.LocalAnalysis.UniquenessCase.UC22
