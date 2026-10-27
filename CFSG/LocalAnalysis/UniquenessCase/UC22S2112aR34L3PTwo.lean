module

public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_12aFR34L3PTwo (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n → IsPowTwo c.n →
    ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
      (LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1) →
      (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
      (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

end CFSG.LocalAnalysis.UniquenessCase.UC22
