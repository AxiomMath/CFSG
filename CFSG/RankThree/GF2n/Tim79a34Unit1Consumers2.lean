module

public import CFSG.RankThree.GF2n.Tim79a34CentreSmall
public import CFSG.RankThree.GF2n.Tim79a34GriessSpS6
public import CFSG.RankThree.GF2n.Tim79a34Sp62CoverLift
public import CFSG.RankThree.GF2n.Tim79a34Sp42CoverLift

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open Matrix CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.ARS.CaseM
open scoped commutatorElement

section Certified

theorem sec34CentreSmallStatement_holds_unit1 : Sec34CentreSmallStatement :=
  sec34CentreSmallStatement_holds griessSpMultiplierExceptionStatement_holds
    sp62CoverLiftStatement_holds sp42CoverLiftStatement_holds

end Certified

end CFSG.RankThree.GF2n.Tim79a
