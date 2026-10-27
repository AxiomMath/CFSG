module

public section

namespace CFSG.ComponentClassification.AS81.HePres.Native

@[expose] def heRWords : List (List Nat) := [[3, 14, 4, 14, 6], [0, 0, 2, 4, 3, 4]]

@[expose] def heRCentWords : List (List Nat) :=
  [[0, 15, 1, 11, 15, 11, 13], [5, 2, 11, 14, 11, 15, 10], [9, 13, 9, 0, 5, 9],
    [8, 1, 12, 3, 6, 9]]

@[expose] def heRWitWord : List Nat := [0]

@[expose] def heRChainBase : List (Fin 8330) := [17, 20, 1]

@[expose] def heRChainWords : Array (List Int) :=
  #[[], [], [2, 2, 2], [-2, 1, 2, -1, 2], [1, 4, 1], [-3, 5, 5, 5], [-1, -1, 5, 1],
    [-3, 7, -5, 4], [-3, 5, 8, 4]]

end CFSG.ComponentClassification.AS81.HePres.Native
