module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main6
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

theorem s22_1_of (D : Data G) (Ch : Choice2011 G) (h111 : F11.R111 D) (h112 : F11.R112 D)
    (hW : H1930 D → ∀ _ : Ctx22 D Ch, InCalW D.M D.T D.U) : S22_1 D Ch := by
  intro h1930 c
  have hH := uc22p22c_hyp11 D (hW h1930 c) c.hU
  refine ⟨h111 ⊥ D.U hH, fun hne => ?_⟩
  have h := h112 ⊥ D.U hH hne
  rwa [uc22p22c_cTilde_bot] at h

end CFSG.LocalAnalysis.UniquenessCase.UC22
