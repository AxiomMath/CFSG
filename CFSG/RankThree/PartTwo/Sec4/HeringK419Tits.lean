module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofAutThree
public import CFSG.RankThree.PartTwo.Sec4.HeringK419TitsLocal

public section

namespace CFSG.RankThree.PartTwo.Sec4

open HeringK419

theorem k419AutThreeInnerTits_holds :
    K419AutThreeInnerTits := by
  intro X _ hX k hk3 hk1
  exact hasTwoWitness_of_reeTitsModel hX hk3 hk1

end CFSG.RankThree.PartTwo.Sec4
