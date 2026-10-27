module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_12aFR2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f : ℕ,
    LieModel (BarInf L) .PSL 2 p f → (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    (∃ b ∈ c.B0, ∃ hb : b ∈ normalizer (L : Set G),
      inducedBarInfAutHom L ⟨b, hb⟩ ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) →
    F08.Thin8 L

@[expose] def S21_12aFR34 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsChev (BarInf L) p → (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

end CFSG.LocalAnalysis.UniquenessCase.UC22
