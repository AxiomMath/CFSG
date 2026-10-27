module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSevenThirteenTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.GapSingleCompA5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.GapSingleCompU34
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQuot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem gap19_7_SingleComponent_holds (hK : Inputs1719.K_U34InvolutionGen) :
    Gap19_7_SingleComponent := by
  intro W _ _ hW Y N hirr hopp hshape ht
  obtain ⟨t, htY, ht2, htm⟩ := ht
  have hYN : Y ≤ normalizer (N : Set (MulAut W)) :=
    hopp ▸ PartOne.Section9.le_normalizer_opp 3 Y
  have htm' : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3 := by
    rwa [CFSG.GroupTheory.mQuot_top_eq_rkIdx] at htm
  rcases hshape with hA | hU
  · exact pRank_five_le_one_of_isAlt_of_rkIdx_le_three hW hirr hYN hA htY ht2 htm'
  · exact (false_of_isU3_two_of_rkIdx_le_three hK hW hirr hYN hU htY ht2 htm').elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
