module

public import CFSG.Quasithin.MS93.Burnside.Sp4AShortB
public import CFSG.Quasithin.MS93.Burnside.Sp4ARig
public import CFSG.Quasithin.MS93.Burnside.Sp4ACoc

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem burnsideSp4A_lemmaC : burnsideSp4A_LemmaC :=
  fun _ _ _ _ _ _ h _ _ _ _ _ hcard hk _ hφs hφ _ hwQ hwL _ hYK hQY hYw hYR =>
    burnsideSp4A_mem_uq_sup_dq h hcard hk hφs hφ hwQ hwL hYK hQY hYw hYR

theorem burnsideSp4A_lemmaR : burnsideSp4A_LemmaR :=
  fun _ _ _ _ _ _ h _ _ _ _ _ hcard hk _ hφs hφ _ hc hνK =>
    burnsideSp4A_rigid_pre_zm h hcard hk hφs hφ hc hνK

end CFSG.Quasithin.MS93.S4L
