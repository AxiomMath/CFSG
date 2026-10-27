module

public import CFSG.LocalAnalysis.StandardType.GGE0ExcE6Shape
public import CFSG.LocalAnalysis.StandardType.GGE0ExcE6NonShape
public import CFSG.LocalAnalysis.StandardType.GGE0ExcTwE6Shape

public section

namespace CFSG.StandardType

theorem ggE0At_E6_holds :
    GGE0At .E6 :=
  ggE0At_of_on ggE0AtOn_E6_shape ggE0AtOn_E6_nonshape

theorem ggE0At_twistedE6_holds :
    GGE0At .twistedE6 :=
  ggE0At_of_on ggE0AtOn_twistedE6_shape ggE0AtOn_twistedE6_nonshape

end CFSG.StandardType
