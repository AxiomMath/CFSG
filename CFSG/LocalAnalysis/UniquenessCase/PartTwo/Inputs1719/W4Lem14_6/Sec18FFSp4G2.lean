module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFSp4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFG2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem k146FFSp4_holds : K146FFSp4 := by
  intro W _ _ hW Y L n _ hL hSp hn hA
  obtain ⟨K, hK, hKf, hcard, hR⟩ := (ffChiefSp4_section hW hL hn hSp hA).2
  exact ⟨by norm_num, K, hK, hKf, hcard, hR⟩

theorem k146FFG2_holds :
    K146FFG2 := by
  intro W _ _ hW Y L n _ hL hG2 hn hodd hA
  exact (ffChiefG2_section hW hL hn hodd hG2 hA).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
