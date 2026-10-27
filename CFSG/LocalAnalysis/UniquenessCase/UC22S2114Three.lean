module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114E3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114GlueD
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114D4Three
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2ThreeHead
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3UThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4Three
import CFSG.LocalAnalysis.UniquenessCase.UC22S218XThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LHead
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218X
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem s21_14_of_residuals
    {D : Data G} {Ch : Choice2011 G}
    (hGA : GriessAllModelsStatement) (hN : uc22p20rNativeGriess) (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h82 : F08.R82 D)
    (hM3 : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q D.M ≤ 3)
    (h13 : PartTwo.SigmaRankThree13 D)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h3 : S21_3 D Ch) (h5 : S21_5 D Ch)
    (h8N : S21_8N D Ch) (h8XT : S21_8XT D Ch) (hR4T : S21_14R4T D Ch)
    (hR3LF : S21_14R3LF D Ch) (hR3LK2 : S21_14R3LK2 D Ch) (hD4T : S21_14D4T D Ch)
    (hK2T : S21_14K2T D Ch) : S21_14 D Ch :=
  s21_14_of_s21_14R D Ch h8N (s21_8X_of_s21_8XT hGA hM3 h8XT)
    (s21_14R_of_residuals hGA hSg h614 h76 h82 hn3 h3 h5
      (s21_14R4_of_s21_14R4T hGA hN hM3 h82 hn3 h3 h5 hR4T)
      (s21_14R3U_of_pRank_le_three hGA hM3)
      (s21_14R3L_of_residuals hGA hSg h614 h76 (isStronglyPEmbedded_three_of_r82 h82) hn3 h3 h5
        hR3LF (s21_14R3LT_of_sigmaRankThree13 hGA hSg hM3 h13) hR3LK2)
      (s21_14D4_of_s21_14D4T hSg h614 h76 hD4T)
      (s21_14K2_of_s21_14K2T hGA hSg h614 h76 hD4T hK2T))

end CFSG.LocalAnalysis.UniquenessCase.UC22
