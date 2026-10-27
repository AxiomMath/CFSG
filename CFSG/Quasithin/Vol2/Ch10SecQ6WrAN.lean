module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrAM
public import CFSG.Quasithin.Vol2.Ch10SecQ6WrIrr

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

theorem hypFix_Ncl_base {A : Subgroup SymFiveWrTwo} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h2 : ∀ a ∈ A, a * a = 1) (hA : A ≠ ⊥) (hbase : ∀ g ∈ A, g.right = 1) : HypFix Ncl A := by
  by_cases hD1 : projSub A 1 = ⊥
  · obtain ⟨D', -, ⟨x1, hx1, hx1D, hcov⟩, u, hu, hufix, d, hd, hdu⟩ :=
      exists_hyperplane_fix (projSub_comm hc zs) (projSub_sq h2 zs)
        (projSub_zs_ne_bot hbase hA hD1)
    obtain ⟨v, hv, hv0, hvfix⟩ := exists_fix_ne_zero (projSub_comm hc 1) (projSub_sq h2 1)
    obtain ⟨x, hxA, hxB, hcovA⟩ := coordPre_cover hbase hx1 hx1D hcov
    obtain ⟨gd, hgdA, hgdr, rfl⟩ := hd
    refine ⟨coordPre A hbase zs D', coordPre_le, ⟨x, hxA, hxB, hcovA⟩, tens v u,
      tens_mem_Ncl hv hu, fun b hb => ?_, gd, hgdA, ?_⟩
    · rw [gP_tens_base (hbase b hb.1), hufix _ hb.2,
        hvfix _ ⟨b, hb.1, hbase b hb.1, rfl⟩]
    · rw [gP_tens_base hgdr, hvfix _ ⟨gd, hgdA, hgdr, rfl⟩]
      exact tens_ne_right hv0 hdu
  · obtain ⟨D', -, ⟨x1, hx1, hx1D, hcov⟩, u, hu, hufix, d, hd, hdu⟩ :=
      exists_hyperplane_fix (projSub_comm hc 1) (projSub_sq h2 1) hD1
    obtain ⟨v, hv, hv0, hvfix⟩ := exists_fix_ne_zero (projSub_comm hc zs) (projSub_sq h2 zs)
    obtain ⟨x, hxA, hxB, hcovA⟩ := coordPre_cover hbase hx1 hx1D hcov
    obtain ⟨gd, hgdA, hgdr, rfl⟩ := hd
    refine ⟨coordPre A hbase 1 D', coordPre_le, ⟨x, hxA, hxB, hcovA⟩, tens u v,
      tens_mem_Ncl hu hv, fun b hb => ?_, gd, hgdA, ?_⟩
    · rw [gP_tens_base (hbase b hb.1), hufix _ hb.2,
        hvfix _ ⟨b, hb.1, hbase b hb.1, rfl⟩]
    · rw [gP_tens_base hgdr, hvfix _ ⟨gd, hgdA, hgdr, rfl⟩]
      exact tens_ne_left hv0 hdu

theorem left_one_eq_of_comm {h : SymFiveWrTwo} (hh : h * wrT = wrT * h) :
    h.left 1 = h.left zs := by
  have h1 : (h * wrT).left 1 = (wrT * h).left 1 := congrArg (fun g : SymFiveWrTwo => g.left 1) hh
  rw [left_mul_apply, left_mul_apply, wrT_left, wrT_left, wrT_right, zs_inv_mul_one,
    mul_one, one_mul] at h1
  exact h1

theorem left_zs_mul {g h : SymFiveWrTwo} (hh : h.left 1 = h.left zs) :
    (g * h).left zs = g.left zs * h.left zs := by
  rw [left_mul_apply]
  rcases zmod2_cases g.right with hr | hr
  · rw [hr, one_inv_mul]
  · rw [hr, zs_inv_mul_zs, hh]

theorem left_zs_inv {g : SymFiveWrTwo} (hg : g.left 1 = g.left zs) :
    g⁻¹.left zs = (g.left zs)⁻¹ := by
  rcases zmod2_cases g.right with hr | hr
  · rw [inv_left_base hr]
  · rw [inv_left_swap_zs hr, hg]

theorem gP_wrT_tens_ne : gP wrT (tens (wv 4) (wv 3)) ≠ tens (wv 4) (wv 3) := by
  rw [gP_tens_swap wrT_right, wrT_left, wrT_left, pv_one, pv_one]
  intro h
  have := congrFun (congrFun h 3) 4
  revert this
  decide

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
