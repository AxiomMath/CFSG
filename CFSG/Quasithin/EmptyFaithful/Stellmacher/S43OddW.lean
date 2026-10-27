module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem Wn_le_stab_of_dist (hA : F53Amalgam H M S) (hs : Sit43 α) {κ : Geo H M}
    (h : dist α κ + 2 ≤ bMin H M) : Wn α ≤ stab κ := by
  refine iSup₂_le fun l hl => ?_
  have hlv : vtype l = false := hs.vtype_of_dist_two hA hl
  have h1 := dist_triangle hA.amalgam.gen l α κ
  exact hs.Zv_le_stab_of_dist_le_false hA hlv (by omega)

theorem Wn_le_Qv_of_dist (hA : F53Amalgam H M S) (hs : Sit43 α) {κ : Geo H M}
    (h : dist α κ + 2 < bMin H M) : Wn α ≤ Qv κ := by
  refine iSup₂_le fun l hl => ?_
  have hlv : vtype l = false := hs.vtype_of_dist_two hA hl
  have h1 := dist_triangle hA.amalgam.gen l α κ
  exact hs.Zv_le_Qv_of_dist_lt_false hlv (by omega)

theorem isElemAbelian_Wn_of_five (hA : F53Amalgam H M S) (hs : Sit43 α) (hb : 5 ≤ bMin H M) :
    IsElemAbelian 2 (Wn α) := by
  have e : Wn α = ⨆ l : {l : Geo H M // dist l α = 2}, Zv l.1 := by
    unfold Wn; exact iSup_subtype'
  rw [e]
  refine isElemAbelian_iSup _ (fun l => isElemAbelian_Zv hA l.1) (fun l l' x hx y hy => ?_)
  have h3 := dist_triangle hA.amalgam.gen l.1 α l'.1
  rw [CosetGeom.dist_comm α l'.1, l.2, l'.2] at h3
  have hxQ : x ∈ Qv l'.1 :=
    hs.Zv_le_Qv_of_dist_lt_false (hs.vtype_of_dist_two hA l.2) (by omega) hx
  exact Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA l'.1 hy).2 x hxQ

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
