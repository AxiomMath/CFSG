module

public import CFSG.Quasithin.Recognition.M22UniqueData
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public meta import CFSG.Quasithin.Recognition.M22UniqueData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads

public section

namespace CFSG.Quasithin.H13

open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

@[expose] def m22Hex01L : List (List (Fin 22)) :=
  [[0, 1, 2, 9, 17, 19], [0, 1, 3, 6, 14, 20], [0, 1, 4, 5, 13, 18], [0, 1, 7, 8, 16, 21],
    [0, 1, 10, 11, 12, 15]]

@[expose] def m22Hex01Others : List (List (Fin 22)) := m22Hex01L.tail

end CFSG.Quasithin.H13
