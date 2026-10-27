
module

public import CFSG.Sporadic.Ly.KeySpec

public noncomputable section

namespace CFSG.RankThree.Native

@[expose] def lyFiveAbar : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![2, 2, 0, 0; 2, 0, 0, 0; 1, 0, 3, 1; 0, 2, 1, 4]

@[expose] def lyFiveBbar : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, 0, 1, 1; 0, 1, 1, 4; 1, 3, 2, 3; 1, 2, 3, 2]

end CFSG.RankThree.Native
