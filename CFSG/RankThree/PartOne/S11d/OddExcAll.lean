module

public import CFSG.RankThree.PartOne.S11d.PlaneOdd
public import CFSG.RankThree.PartOne.MB3.OddOutExceptional

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.RankThree.PartOne.OutStructure

theorem oddExceptionalOut_holds
    : OddExceptionalOut := by
  intro p T _ t ℓ f hp hp5 hℓ hℓ2 ht hch
  have hp3 : p ≠ 3 := by omega
  have hp2 : p ≠ 2 := by omega
  cases t
  case G2 =>
    by_cases h3 : ℓ = 3
    · subst h3
      exact outPNice_G2_three hp hch
    · exact outPNice_G2_odd hp hℓ2 h3 hch
  case F4 => exact outPNice_F4_odd hp hℓ2 hch
  case E6 => exact outPNice_E6_gen hp hp3 hp2 hch
  case E7 => exact outPNice_E7_gen hp hp2 hch
  case E8 => exact outPNice_E8_gen hp hch
  case twistedE6 => exact outPNice_twistedE6_gen hp hp3 hch
  case trialityD4 => exact outPNice_trialityD4_odd hp hℓ2 hch
  all_goals exact absurd ht (by simp [chevalleyExceptionalTags])

end CFSG.RankThree.PartOne
