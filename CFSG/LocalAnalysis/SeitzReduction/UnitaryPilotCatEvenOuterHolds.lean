module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterOmegaExc

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank


theorem catSUmEvenOuterAt_of_typeDet {m : ℕ} (hm : 4 ≤ m) (hdet : SUmEvenTypeDetAt m) :
    CatSUmEvenOuterAt m :=
  catSUmEvenOuterAt_of_open_families (catSUmEvenOuterFamilyAt_PSL hm hdet)
    (catSUmEvenOuterFamilyAt_PSU hm hdet) (catSUmEvenOuterFamilyAt_PSp hm hdet)
    (catSUmEvenOuterFamilyAt_POmegaPlus hm hdet) (catSUmEvenOuterFamilyAt_POmegaMinus hm hdet)
    (catSUmEvenOuterFamilyAt_G2 hm hdet) (catSUmEvenOuterFamilyAt_F4 hm hdet)
    (catSUmEvenOuterFamilyAt_E6 hm hdet) (catSUmEvenOuterFamilyAt_E7 hm hdet)
    (catSUmEvenOuterFamilyAt_E8 hm hdet) (catSUmEvenOuterFamilyAt_twistedE6 hm hdet)
    (catSUmEvenOuterFamilyAt_trialityD4 hm hdet)

theorem catSUmEvenOuterAt {m : ℕ} (hm : 4 ≤ m) : CatSUmEvenOuterAt m :=
  catSUmEvenOuterAt_of_typeDet hm (sumEvenTypeDetAt hm)

end CFSG.SeitzReduction.UnitaryPilot
