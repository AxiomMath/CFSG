module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13a
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.UC22P2121a
import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem uc22s2121e3_r847Four_of_r847E3Thin {D : Data G} {Ch : Choice2011 G}
    (h847 : R847E3Thin D) (h61 : UC6.R6_1 D) (c : Ctx21 D Ch) (hH : Hyp2120 D c) :
    R847Four D := by
  intro Y hY X hXY q hq hq2 hXq p hp hthin
  rcases h847 Y hY (hH.2.1 Y hY).1 hthin X hXY q hq hq2 hXq p hp with h1 | ⟨rfl, h2⟩
  · exact h1
  · have h1 := uc22p2121_pRank_centE_le_one h61 c hH hp
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
