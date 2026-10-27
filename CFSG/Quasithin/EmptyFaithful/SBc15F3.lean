module

public import CFSG.Quasithin.EmptyFaithful.SBc15F3Wr
public import CFSG.Quasithin.EmptyFaithful.SBc15F3Cls

public section

namespace CFSG.Quasithin

namespace SBc15

theorem weakW_l32 : WeakW (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ⊤ :=
  weakW_top_of_local (by rw [L3.card_SL32]; norm_num) L3.local_good_SL32

end SBc15

end CFSG.Quasithin
