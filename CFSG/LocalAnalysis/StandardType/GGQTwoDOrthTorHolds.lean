module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDGN6Assembly
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorJ

public section

namespace CFSG.StandardType.QTwo

theorem ggQTwoDOrthJInput_holds : GGQTwoDOrthJInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ hcfg Φ hF h5 hZ =>
    qtwoOrth_jlabel_of_frame hcfg Φ hF (by omega) hZ

theorem qTwoOrthJAnchorInput_holds : QTwoOrthJAnchorInput :=
  fun _ _ _ _ hp _ _ _ _ Φ hF h5 _ hx _ hJc =>
    qtwoOrth_jAnchor_of_frame hp Φ hF (by omega) hx hJc

theorem qTwoOrthJAnchor4Input_holds : QTwoOrthJAnchor4Input :=
  fun _ _ _ _ hp _ _ _ _ Φ hF h4 _ hx _ hJc =>
    qtwoOrth_jAnchor_of_frame hp Φ hF h4 hx hJc

end CFSG.StandardType.QTwo

end
