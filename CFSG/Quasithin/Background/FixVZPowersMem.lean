module

public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem mem_fixV_zpowers_iff_apply {g : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v := by
  constructor
  · intro h; exact h g (Subgroup.mem_zpowers g)
  · intro h x hx
    have : Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut V) v := by
      rw [Subgroup.zpowers_le]
      exact h
    exact this hx

end CFSG.Quasithin
