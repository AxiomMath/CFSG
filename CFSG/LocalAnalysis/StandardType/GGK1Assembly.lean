module

public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGMultTableCl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggK0MainBS_cl_of_lanes (hA : GGK0MainBS GGKacGenericClA GGMultValidCl)
    (hC : GGK0MainBS GGKacGenericClC GGMultValidCl)
    (hD : GGK0MainBS GGKacGenericClD GGMultValidCl) :
    GGK0MainBS GGKacGenericCl GGMultValidCl := by
  intro p lab hlab hgen
  rcases ggKacGenericCl_lanes hlab hgen with h | h | h
  · exact hA p lab hlab h
  · exact hC p lab hlab h
  · exact hD p lab hlab h

end CFSG.StandardType

end
