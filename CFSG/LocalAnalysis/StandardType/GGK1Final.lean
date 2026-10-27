module

public import CFSG.LocalAnalysis.StandardType.GGK1ALane
public import CFSG.LocalAnalysis.StandardType.GGK1CLane
public import CFSG.LocalAnalysis.StandardType.GGK1DLane
public import CFSG.LocalAnalysis.StandardType.GGK1Assembly

public section

namespace CFSG.StandardType

theorem ggK0MainBS_cl_of_schur (hS : GGK0Schur GGKacGenericCl) :
    GGK0MainBS GGKacGenericCl GGMultValidCl :=
  ggK0MainBS_cl_of_lanes
    (ggK0MainBS_clA fun p lab hlab h => hS p lab hlab h.1)
    (ggK0MainBS_clC fun p lab hlab h => hS p lab hlab h.1)
    (ggK0MainBS_clD fun p lab hlab h => hS p lab hlab h.1)

theorem ggK0Main_cl_of_schur (hS : GGK0Schur GGKacGenericCl) :
    GGK0Main GGKacGenericCl GGMultValidCl :=
  (ggK0MainBS_cl_of_schur hS).toB.toMain

end CFSG.StandardType

end
