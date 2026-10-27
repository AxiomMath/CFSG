module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112L2Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_12a (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsChev (BarInf L) p → IsL2Odd (Bar2 L) p

theorem s21_12_of_s21_12a {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch)
    (h847 : R847Four D) (hsig : D.sig.Nonempty) (h : S21_12a D Ch) : S21_12 D Ch := by
  intro hH c L hL p hp hp2 hch
  have hLp := h hH c L hL p hp hp2 hch
  exact ⟨hLp, s21_12L2_of_r847Four h5 h847 hsig hH c hL hp hp2 hLp⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
