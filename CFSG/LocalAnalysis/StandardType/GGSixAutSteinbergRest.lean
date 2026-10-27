module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE7
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank


theorem ggAutStructureRest_of_remaining (hU : GGAutStructureAt .PSU)
    (hSp : GGAutStructureAt .PSp) (hP : GGAutStructureAt .POmegaPlus)
    (hM : GGAutStructureAt .POmegaMinus) (hE6 : GGAutStructureAt .E6)
    (h2E6 : GGAutStructureAt .twistedE6) : GGAutStructureRest :=
  ⟨hU, hSp, hP, hM, ggAutStructureAt_F4, hE6, ggAutStructureAt_E7, ggAutStructureAt_E8, h2E6⟩

theorem ggAutStructureRest_of_models (hU : GGAutStructureAt .PSU)
    (hSp : GGAutStructureAt .PSp) (hP : GGAutModelAt .POmegaPlus)
    (hM : GGAutModelAt .POmegaMinus) (hE6 : GGAutModelAt .E6)
    (h2E6 : GGAutModelAt .twistedE6) : GGAutStructureRest :=
  ggAutStructureRest_of_remaining hU hSp (ggAutStructureAt_of_autModelAt hP)
    (ggAutStructureAt_of_autModelAt hM) (ggAutStructureAt_of_autModelAt hE6)
    (ggAutStructureAt_of_autModelAt h2E6)

end CFSG.StandardType
