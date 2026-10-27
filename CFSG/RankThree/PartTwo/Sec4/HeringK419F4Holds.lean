module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofAutThree
import CFSG.RankThree.PartTwo.Sec4.HeringK419F4
import CFSG.RankThree.PartTwo.Sec4.HeringK419F4Out

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Item419Res3 HeringK419


theorem k419AutThreeInnerF4_holds : K419AutThreeInnerF4 := by
  intro X _ n hX k hk3 hk1
  exact ReeF4.hasTwoWitness_of_reeTitsModel hX hk3 hk1

theorem k419AutThreeOuterF4_holds : K419AutThreeOuterF4 := by
  intro X _ n hX β hβ3 hβ
  exact ReeF4.hasOuterWitness_of_reeTitsModel hX β hβ3 hβ

end CFSG.RankThree.PartTwo.Sec4
