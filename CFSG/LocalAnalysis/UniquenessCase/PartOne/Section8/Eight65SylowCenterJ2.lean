module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65SylowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Inversion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem sylowCenterInverted_of_isSpor_j2
    {Y : Type} [Group Y] [Finite Y] (hY : IsSpor Y .J2) : SylowCenterInverted Y := by
  unfold SylowCenterInverted
  intro Q z hzQ hzc hz3
  obtain ⟨t, -, ht⟩ := j2_inverting_of_isSpor hY Q hzQ hzc hz3
  exact ⟨t, ht⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
