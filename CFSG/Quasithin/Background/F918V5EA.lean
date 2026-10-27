module

public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem f918v5e_mem_fixV_zpowers {b : MulAut W} {x : W} :
    x ∈ fixV (Subgroup.zpowers b) ↔ b x = x :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

end CFSG.Quasithin
