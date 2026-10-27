module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Thirteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22th
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSmall
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallT7
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallResults
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenElevenRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34T8
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154RT8
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLaughlin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrime
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormNat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTable
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTorus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3List
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAbsIrr
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKSchur2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAutRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKCover3Rank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKSchur
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKIso
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNotJ2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKPerfType
import CFSG.RankThree.PartTwo.Sec11.Item116R2K1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]


theorem r15_13Small_of_inputs (D : Data G) (hx : DataExt D) (hSg : UC6S846.SigmaStd D)
    (h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h126 : R126 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h119 : F11.R119 D) (h77eq : F07.R77Eq D) (h82 : F08.R82 D)
    (h869 : F08.R869 D) (h880 : F08.R880 D) (h111 : F11.R111 D) (h112 : F11.R112 D) :
    R15_13Small D := by
  intro V₀ V L h hsmall hL
  have hσ : D.sig = D.sig1 := h1219 V₀ V h.hyp151.hyp125
  have h129 : R129_1 D := r129_1_of_r127 _ h127
  have h1217 : R1217 D := r1217_of_twelve_seventeen _ hx h61 h127 h1214
  have h115 : F11.R115 D := uc22p22q_r115_of _ hx h61
  have h153 : R15_3Small D :=
    fifteen_three_small _ hx rMcLaughlin_holds rJPrime153_holds rNormNat153_holds
      rTable137_holds rTorus3_153_holds rRank3List153_holds rAbsIrr153_holds rSimple153_holds
      h61 h63 rSchur2_153_holds h127 h115 h119 h1217 h1214 h82 h880 (r1111_153_holds _ hx h61)
      rAutRank153_holds
      (rCover3Rank153_holds CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
      rRank3Omega153_holds rSchur153_holds rIso153_holds rNotJ2_holds rPerfType153_holds
  have hT7 : RT7Small D := rt7_of_fifteen_three_small _ h153 h129 h1217
  have h156 : R15_6Small D := fifteen_six_small _ h129 h1217 hT7 hSg hσ
  have h159 : R15_9Small D := fifteen_nine_small _ h1217 h156 (fifteen_eight_small _ h1217 h156)
  have hCyc := CFSG.RankThree.PartTwo.Sec11.cyclicSylowThreeOutAbelian_holds
  have hT8 : RT8 D := s16c34_rt8_of_small _ h153 h1217 h127
    (s16h_r1110W_holds _ hSg h61 h63 h77eq h869 h111 h112 thinList13_holds hCyc) hσ
  exact s16c34_fifteen_thirteen _ hSg hσ h129 h61 h126 h127 h1217
    (r1110Core_holds _ hSg h61 h63 h77eq h869 h111 h112 thinList13_holds hCyc)
    (s16c34_r1111_of_153 (r1111_153_holds _ hx h61)) h115 h159
    (s16c34_fifteen_eleven _ h1217 h159 hT7 hT8) (s16c34_fifteen_twelve _ h129 h1217 hT7)
    V₀ V L h hsmall hL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
