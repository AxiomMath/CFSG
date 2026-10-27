module

public import CFSG.RankThree.PartOne.S9.OddCore.TorsionElementary
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionExtraspecialC
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionQD32
public import CFSG.RankThree.PartOne.S9.Planes.SecondCenter

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.RankThree.PartOne.Torsion37
open scoped commutatorElement

theorem extraspecialTwoActionOddCoreTorsionLifting_of_second_center
    (hET32 : ExtraspecialThirtyTwoFixedRankTwoAction) (hPG2C : PGOddSecondCenterPrimeTorsion) :
    ExtraspecialTwoActionOddCoreTorsionLifting := by
  intro G _ _ q A R Q D hq hq2 hq5 hA hAR hRA hRQD hQn hQp hDQ hDchar _ hRD hshape hrank
  obtain ⟨hRext, hR32, hs⟩ := qd32_facts hRQD
  have ha := exists_fixed_point_free_of_commutator hA hAR hRA hRext hR32
  have hDn : D.Normal := OddCore37.normal_of_characteristic hDQ hDchar
  rcases hshape with ⟨hDel, hDcard⟩ | ⟨hDexp, hDcard, hcomm, hZ, hΦ⟩
  · exact omegaOne_eq_of_elementary hET32 hPG2C hq hq2 hq5 hA hAR hRext hR32 ha hQp hDQ hRD
      hDel hDcard hrank
  · exact omegaOne_eq_of_extraspecial hET32 hq hq2 hq5 hA hAR hRA hRext hR32 ha hs hQp hDQ hRD
      hDexp hDcard hcomm hZ hΦ hrank

theorem extraspecialTwoActionOddCoreTorsionLifting_of
    (hET32 : ExtraspecialThirtyTwoFixedRankTwoAction) :
    ExtraspecialTwoActionOddCoreTorsionLifting :=
  extraspecialTwoActionOddCoreTorsionLifting_of_second_center hET32
    pgOddSecondCenterPrimeTorsion

end CFSG.RankThree.PartOne
