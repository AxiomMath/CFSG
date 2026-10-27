module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.Pair
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Subgroup

theorem kGenSpans_of_isSpor_J1 {K : Type} [Group K] [Finite K]
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor K .J1) {B R : Subgroup K}
    (hBR : IsKGenPair B R) : KGenSpans B R := by
  have hcard := (CFSG.LocalAnalysis.UniquenessCase.UC22.kJ1_holds K h).1
  have hdvd := Subgroup.card_subgroup_dvd_card R
  rw [hBR.2.2.1, hcard] at hdvd
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen
