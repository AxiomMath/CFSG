module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open scoped Pointwise

section Section21c

variable {G : Type} [Group G] [Finite G]

@[expose] def LieRankOneEven (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, IsL2 X n ∨ IsSz X n ∨ IsU3 X n

@[expose] def S21_14 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_19 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ K ∈ calC D.M, L ≠ K →
    (L.subgroupOf D.M).Normal →
    (IsJ1 (Bar2 L) ∨ ∃ p : ℕ, p.Prime ∧ 5 < p ∧ IsL2Odd (Bar2 L) p) →
      ¬ ((∃ n : ℕ, IsL2 (Bar2 K) n) ∨ (∃ m : ℕ, IsPowTwo m ∧ IsU3 (Bar2 K) m) ∨ IsJ1 (Bar2 K) ∨
        ∃ q : ℕ, q.Prime ∧ IsL2Odd (Bar2 K) q)

end Section21c

end CFSG.LocalAnalysis.UniquenessCase.UC22
