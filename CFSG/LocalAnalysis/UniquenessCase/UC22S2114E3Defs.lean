module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_14K2T (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    (∃ f : ℕ, 4 ∣ f ∧ (IsSp4 (BarInf L) f ∨ IsG2 (BarInf L) f ∨ IsU4 (BarInf L) f ∨
        Is3D4 (BarInf L) f) ∧
      ∀ p ∈ D.sig, p ∣ 2 ^ f + 1 ∨ (Is3D4 (BarInf L) f ∧ p ∣ 2 ^ (2 * f) - 2 ^ f + 1)) →
    D.k = 2 → 3 ≤ c.n → 4 ∣ c.n → c.B0 ≤ normalizer (L : Set G) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_14D4T (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    (∃ f : ℕ, Is3D4 (BarInf L) f) → (c.n = 3 ∨ c.n = 6) →
    (D.k = 1 → c.n = 3 ∧ c.B0 ≤ normalizer (D.T : Set G)) → c.B0 ≤ normalizer (L : Set G) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → (∀ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p L) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_14R4T (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ((LieModel (BarInf L) .PSL 5 2 1 ∧ ¬ 4 ∣ c.n) ∨
      ((LieModel (BarInf L) .PSL 6 2 1 ∨ LieModel (BarInf L) .PSL 7 2 1) ∧ D.k = 1)) →
    3 ≤ c.n → c.B0 ≤ normalizer (L : Set G) → (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    (D.k = 1 → Odd c.n ∧ c.B0 ≤ normalizer (D.T : Set G)) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_8XT (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ,
    (IsL3 (BarInf L) n ∨ IsG2 (BarInf L) n ∨ Is3D4 (BarInf L) n ∨
      LieModel (BarInf L) .twistedF4 0 2 n ∨ IsU4 (BarInf L) n) →
    ¬ IsPowTwo n → False

end CFSG.LocalAnalysis.UniquenessCase.UC22
