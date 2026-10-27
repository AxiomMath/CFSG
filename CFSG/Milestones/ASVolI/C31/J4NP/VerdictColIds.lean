module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F918U7

public section

namespace CFSG.ASVolI

@[expose] def burnsideJ4NP_colIds0 : List ℕ :=
  (List.range' 5 472).filter fun k => k ∉ [11, 36, 39, 42, 63, 66, 73, 76, 81, 89, 93, 98, 102,
    103, 106, 107, 112, 124, 133, 134, 135, 136, 166, 219, 266, 267, 378, 385, 389, 464]

@[expose] def burnsideJ4NP_colIds1 : List ℕ :=
  (List.range' 477 376).filter fun k => k ∉ [480, 486, 515, 516, 527, 532, 539, 542, 543, 552, 715]

@[expose] def burnsideJ4NP_colIds2 : List ℕ :=
  (List.range' 853 274).filter fun k => k ∉ [867, 871, 895, 905, 916, 937, 959, 1013, 1025, 1077,
    1085, 1122, 1124]

@[expose] def burnsideJ4NP_colIds3 : List ℕ :=
  (List.range' 1127 201).filter fun k => k ∉ [1216, 1244, 1260, 1277, 1284, 1322, 1326]

end CFSG.ASVolI
