module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_14R4 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    (∃ l f : ℕ, 4 ≤ l ∧ PartTwo.S17.CHasLieRank (BarInf L) l f) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_14R3U (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    (∃ f : ℕ, LieModel (BarInf L) .PSU 6 2 f ∨ LieModel (BarInf L) .PSU 7 2 f) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_14R3L (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    (∃ f : ℕ, LieModel (BarInf L) .PSL 4 2 f ∨ LieModel (BarInf L) .PSp 3 2 f ∨
      IsOmega8m (BarInf L) f) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_14D4 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    (∃ f : ℕ, Is3D4 (BarInf L) f) → D.k = 1 → c.n = 3 →
    c.B0 ≤ normalizer (D.T : Set G) → c.B0 ≤ normalizer (L : Set G) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_14K2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ((∃ f : ℕ, 2 ≤ f ∧ (IsSp4 (BarInf L) f ∨ IsG2 (BarInf L) f ∨ IsU4 (BarInf L) f ∨
        IsU5 (BarInf L) f)) ∨ ∃ f : ℕ, Is3D4 (BarInf L) f) →
    D.k = 2 → 3 ≤ c.n → c.B0 ≤ normalizer (L : Set G) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_14L34 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    IsL3 (BarInf L) 2 → D.k = 2 → c.n = 4 → c.B0 ≤ normalizer (L : Set G) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

end CFSG.LocalAnalysis.UniquenessCase.UC22
