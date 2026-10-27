module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18CaseII
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18CaseL2Sz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18CaseSp4G2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18CaseU4U54
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU54

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w4Lem14_6Sec18_of_kfacts
    (hFFL2 : K146FFL2) (hFFSz : K146FFSz) (hFFU54 : K146FFU54) (hFFSp4 : K146FFSp4)
    (hFFG2 : K146FFG2) (hFFU4 : K146FFU4)
    (hbSp4G2 : W4Lem4_17Sp4G2N) (hbU : W4Lem4_17U4U5N)
    (hModL2 : K146ModL2) (hModSz : K146ModSz) (hModSp4 : K146ModSp4) (hModG2 : K146ModG2)
    (hModU4 : K146ModU4) (hInvU54 : K146U54InvRank) (hOutU54 : K146U54OuterInv)
    (hA : K146Om6mA) (hTwo : K146Sp4TwoNat) (hIsoOm4m : K146NatIsoOm4m)
    (hIsoU4 : K146NatIsoU4) :
    W4Lem14_6Sec18 := by
  have hModU54 : K146ModU54 := k146ModU54_of hInvU54 hOutU54
  refine w4Lem14_6Sec18_of_concl ?_
  intro W _ _ hW Y L X n hK hO2 hB hL hX hcase hm hle hfix
  rcases hfix with hi | hii
  · rcases hcase with
      ⟨hLS | hLS, hn, hc⟩ | ⟨rfl, rfl, hU5⟩ | ⟨rfl, hodd, hn, hSp | hG2⟩ | ⟨rfl, hn, hU4⟩
    · exact concl146_of_caseI_L2 hModL2 hIsoOm4m hW hK hO2 hB hL hX hLS hn hc hi hm hle
    · exact (false_of_caseI_Sz hModSz hW hO2 hB hL hX hLS hn hi hm hle).elim
    · exact (false_of_caseI_U54 hbU hModU54 hW hO2 hB hL hX hU5 hi hm hle).elim
    · exact concl146_of_caseI_Sp4 hbSp4G2 hModSp4 hTwo hW hO2 hB hL hX hSp hodd hn hi hm hle
    · exact concl146_of_caseI_G2 hbSp4G2 hModG2 hW hO2 hB hL hX hG2 hodd hn hi hm hle
    · exact concl146_of_caseI_U4 hbU hModU4 hA hIsoU4 hW hO2 hB hL hX hU4 hn hi hm hle
  · exact concl146_of_caseII hFFL2 hFFSz hFFU54 hFFSp4 hFFG2 hFFU4 hW hO2 hB hL hX hcase hii

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
