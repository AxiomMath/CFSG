module

public import CFSG.RankThree.PartOne.S15K.Row1Layer
public import CFSG.RankThree.PartOne.S15K.Row2Layer
public import CFSG.RankThree.PartOne.S15K.OrthLayer

public section

namespace CFSG.RankThree.PartOne.S15K

theorem kf157c_of_rowFive (hS13 : Sec13Avail) (h5 : LayerRowFive) : KF157c :=
  kf157c_of_layerRows hS13 layerRowOne layerRowTwo layerRowThree layerRowFour h5

theorem kf158Commc_of_rowFive (hS13 : Sec13Avail) (h5 : LayerRowFive) : KF158Commc :=
  kf158Commc_of_layerRows hS13 layerRowOne layerRowTwo layerRowThree layerRowFour h5

end CFSG.RankThree.PartOne.S15K
