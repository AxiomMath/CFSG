module

public import CFSG.Walter.Ree.Thompson2.BaseGrp.Main
public import CFSG.Walter.Ree.Thompson2.BaseGrp.Y

public section

namespace CFSG.Walter.Ree.T2

theorem baseExists : BaseExists :=
  BaseGrp.baseExists_of fun _ _ _ _ _ _ hk _ h9 h3 hT hJ =>
    BaseGrp.exists_tY_of_nine hk h9 h3 hT hJ

end CFSG.Walter.Ree.T2
