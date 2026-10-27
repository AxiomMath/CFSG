module

public import CFSG.RankThree.PartOne.FOC.Final
public import CFSG.RankThree.PartOne.FOC.ExcD4
public import CFSG.RankThree.PartOne.FOC.ExcRee4
public import CFSG.RankThree.PartOne.FOCD.G2Even
public import CFSG.RankThree.PartOne.FOCD.G2Odd
public import CFSG.RankThree.PartOne.FOCD.Sporadic
public import CFSG.RankThree.PartOne.S11d.OutPCyclicThetaClosed

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Assembly CFSG.Assembly.LowTwoRank

section Exc


theorem FOC.fieldInnerExc_closed : FOC.FieldInnerExc := by
  refine FOCD.fieldInnerExc_of_idx fun d hd => ?_
  cases d with
  | G2 q =>
    rcases hd with ⟨h2, h1⟩ | h2
    · exact FOCD.fieldInnerIdx_G2_odd q h2 h1
    · exact FOCD.fieldInnerIdx_G2_even q h2
  | F4 q => exact FOCD.fieldInnerIdx_F4 q hd.1 hd.2
  | trialityD4 q => exact FOC.fieldInnerIdx_trialityD4 q hd
  | suzuki m => exact FOCD.fieldInnerIdx_suzuki m
  | reeG2 m =>
    subst hd
    exact FOCD.fieldInnerIdx_reeG2_one
  | reeF4 m => exact FOC.fieldInnerIdx_reeF4 m
  | tits => exact FOCD.fieldInnerIdx_tits
  | A _ _ => exact hd.elim
  | twistedA _ _ => exact hd.elim
  | B _ _ => exact hd.elim
  | C _ _ => exact hd.elim
  | D _ _ => exact hd.elim
  | twistedD _ _ => exact hd.elim
  | E6 _ => exact hd.elim
  | E7 _ => exact hd.elim
  | E8 _ => exact hd.elim
  | twistedE6 _ => exact hd.elim

end Exc

section Griess


theorem FOC.fieldOnComponentOuter_of_griess
    (hGriess : CFSG.Open.GriessAllModelsStatement)
    (hSLB : N143.SectionListBound) : FieldOnComponentOuter := by
  exact fieldOnComponentOuter_of_residuals TCB.tauCetiCatalogBridge
    (sec6EightSection_of_griess hGriess) hSLB FOCD.fieldInnerSpor FOC.fieldInnerExc_closed

end Griess

end CFSG.RankThree.PartOne
