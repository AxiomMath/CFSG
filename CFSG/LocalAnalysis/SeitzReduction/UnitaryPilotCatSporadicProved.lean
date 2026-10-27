module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatSporadic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

section Clause

theorem catSUmSporadicAt {m : ℕ} (hm : 4 ≤ m) : CatSUmSporadicAt m :=
  catSUmSporadicAt_of_monster ComponentClassification.CatLeafProof.monsterInnerInput
    ComponentClassification.CatLeafProof.monsterLocalComponentsInput hm

theorem catSUmSporadicAtF_six_one : TwistedE6Pilot.CatSUmSporadicAtF 6 1 :=
  catSUmSporadicAtF_six_one_of_monster ComponentClassification.CatLeafProof.monsterInnerInput
    ComponentClassification.CatLeafProof.monsterLocalComponentsInput

end Clause

section Family

theorem seitzExclusion_highPSU_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    SeitzExclusion HighPSU :=
  seitzExclusion_highPSU_of_cat_inputs hGLS fun _ hm => catSUmSporadicAt hm

end Family

end CFSG.SeitzReduction.UnitaryPilot
