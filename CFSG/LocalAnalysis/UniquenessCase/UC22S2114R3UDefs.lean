module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_14R3UF (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ∀ f : ℕ, (LieModel (BarInf L) .PSU 6 2 f ∨ LieModel (BarInf L) .PSU 7 2 f) →
    (∀ r : ℕ, r.Prime → r ∣ 2 ^ c.n - 1 → r ∣ f) →
    D.k = 1 → Odd c.n → 3 ≤ c.n → c.B0 ≤ normalizer (D.T : Set G) →
    c.B0 ≤ normalizer (L : Set G) → (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

end CFSG.LocalAnalysis.UniquenessCase.UC22
