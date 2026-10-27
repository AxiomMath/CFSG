module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.H13.A5S1327za

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

section Replacement

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_sup_of_commute {X Y : Subgroup G} (hX : IsElemAbelian 2 X)
    (hY : IsElemAbelian 2 Y) (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) : IsElemAbelian 2 (X ⊔ Y) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hX hY hc

end Replacement

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem thompsonJ_T0e : thompsonJ S.T0e = thompsonJ T := by
  refine B6.thompsonJ_eq_of_le (S := T) (R := S.T0e)
    (fun x hx => Subgroup.mem_inf.mpr ⟨thompsonJ_le_self T hx, ?_⟩) inf_le_left
  have := Subgroup.mem_centralizer_iff.mp (S.thompsonJ_le_centralizer_V2 hx) S.e2 S.e2_mem_V2
  exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm

end Setting

end CFSG.Quasithin.H13.A5
