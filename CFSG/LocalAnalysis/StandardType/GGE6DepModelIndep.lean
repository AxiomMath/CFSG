module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs

public section

namespace CFSG.StandardType

namespace E6Dep

@[expose] def cartanE6 : Fin 6 → Vec6 :=
  ![![2, 0, 2, 0, 0, 0], ![0, 2, 0, 2, 0, 0], ![2, 0, 2, 2, 0, 0], ![0, 2, 2, 2, 2, 0],
    ![0, 0, 0, 2, 2, 2], ![0, 0, 0, 0, 2, 2]]

@[expose] def indepGens : Fin 6 → Mat6 := fun i => reflMat (cartanE6 i) ((1 : Mat6) i)

end E6Dep

end CFSG.StandardType

end
