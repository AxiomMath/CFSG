module

public import CFSG.Quasithin.Background.ConjTransport
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.ConjTransport

variable {V : Type*} [CommGroup V]

theorem rkIdx_fixV_map_conj (X : Subgroup (MulAut V)) (g : MulAut V) :
    rkIdx (fixV (X.map (MulAut.conj g).toMonoidHom)) = rkIdx (fixV X) := by
  unfold rkIdx
  rw [index_fixV_map_conj]

end CFSG.Quasithin.ConjTransport
