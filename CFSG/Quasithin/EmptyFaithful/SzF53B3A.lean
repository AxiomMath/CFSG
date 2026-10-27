module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3Defs
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom

namespace F53B3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem three_le_bAt (hB : B3Base H M S) (x : Geo H M) : 3 ≤ bAt x := by
  have h := bMin_le_bAt (H := H) (M := M) x
  rw [hB.b_eq] at h
  exact h

theorem zv_le_qv_of_dist (hB : B3Base H M S) {x y : Geo H M} (h : dist x y ≤ 2) :
    Zv x ≤ Qv y :=
  Zv_le_Qv_of_dist_lt (by have := three_le_bAt hB x; omega)

theorem zv_le_stab_of_dist (hB : B3Base H M S) {x y : Geo H M} (h : dist x y ≤ 3) :
    Zv x ≤ stab y :=
  Zv_le_stab_of_dist_le hB.amalgam (by have := three_le_bAt hB x; omega)

theorem vn_le_qv_of_dist (hB : B3Base H M S) {x y : Geo H M} (h : dist x y ≤ 1) :
    Vn x ≤ Qv y := by
  refine iSup₂_le fun μ hμ => zv_le_qv_of_dist hB ?_
  have h1 : dist μ x = 1 := by
    rw [CosetGeom.dist_comm]
    exact dist_eq_one_iff_adj.mpr hμ
  have h2 := CosetGeom.dist_triangle hB.amalgam.amalgam.gen μ x y
  omega

theorem vn_le_stab_of_dist (hB : B3Base H M S) {x y : Geo H M} (h : dist x y ≤ 2) :
    Vn x ≤ stab y := by
  refine iSup₂_le fun μ hμ => zv_le_stab_of_dist hB ?_
  have h1 : dist μ x = 1 := by
    rw [CosetGeom.dist_comm]
    exact dist_eq_one_iff_adj.mpr hμ
  have h2 := CosetGeom.dist_triangle hB.amalgam.amalgam.gen μ x y
  omega

theorem zv_le_zv_of_adj (hB : B3Base H M S) {β α : Geo H M} (hβ : vtype β = false)
    (h : (graph (H ⊔ M) H M).Adj β α) : Zv β ≤ Zv α :=
  (Zv_eq_omegaOneCenter_inf hB.amalgam (show α ∈ nbrs β from h) (hB.central β hβ)).2

theorem comm_vn_vn_of_dist (hB : B3Base H M S) {β γ : Geo H M} (h : dist β γ = 2) :
    ⁅Vn β, Vn γ⁆ ≤ Vn β ⊓ Vn γ := by
  have h' : dist γ β = 2 := by rw [CosetGeom.dist_comm]; exact h
  exact commutator_le_inf_of_normalizes
    ((vn_le_stab_of_dist hB h.le).trans (stab_le_normalizer_Vn γ))
    ((vn_le_stab_of_dist hB h'.le).trans (stab_le_normalizer_Vn β))

end F53B3

end CFSG.Quasithin
