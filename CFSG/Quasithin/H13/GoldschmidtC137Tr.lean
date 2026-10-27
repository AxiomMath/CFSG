module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin CFSG.Open

section Tr

variable {W W' : Type*} [CommGroup W] [CommGroup W'] (φ : W ≃* W')

theorem conjAut_eq_map_gc (g : MulAut W) (A : Subgroup (MulAut W)) :
    B1.conjAut g A = A.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_map_equiv]
  simp

end Tr

end CFSG.Quasithin.H13.U3.GC137
