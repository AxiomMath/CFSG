module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_8N (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, IsSp4 (BarInf L) n → ¬ IsPowTwo n →
    ∀ r : ℕ, r.Prime → r ∣ 2 ^ n - 1 →
      (IsSp4 (Bar2 L) n ∧ (L.subgroupOf D.M).Normal ∧ ∃ t ∈ D.T, ActsNontrivOnDiagram L t) ∧
      (Odd n ∧ D.k = 1) ∧ ∃ X : Subgroup G, Nat.card X = r ∧ X ≤ L ∧ X ∈ uniqueSet D.M

end CFSG.LocalAnalysis.UniquenessCase.UC22
