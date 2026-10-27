module

public import CFSG.Quasithin.MS93.S4A44Nabla

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem s44_of (h32 : S32) (h43 : S43) (h441 : S4A.S441) (h442 : S4A.S442)
    (hFFc : S4A.S4CFFc) : S44 :=
  S4A.s44_of_steps h441 h442 (S4A.s444_of h32 h43 h441) (S4A.s445_of h32 h43 h441 h442 hFFc)
    (S4A.s44End_of h32 h43 h441 h442 hFFc (S4A.endNabla_of h32 h43 h441 h442 hFFc))

end CFSG.Quasithin.MS93
