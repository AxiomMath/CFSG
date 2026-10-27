module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KLieRest
public import CFSG.RankThree.PartTwo.Sec21.Hering214KSp6

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.Blueprint
open Hering214

namespace Hering214

theorem item214BarLieRest_holds : Item214BarLieRest :=
  fun _ _ _ hX Ē Ū hd => eInvFourFact_of_statedModel_sp62 hX Ē Ū hd

end Hering214

theorem item214BarLie_of_3D4
    (h : Item214BarLie3D4') : Item214BarLie :=
  item214BarLie_of_rest item214BarLieRest_holds h

end CFSG.RankThree.PartTwo.Sec21
