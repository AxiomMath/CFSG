module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2RootDef

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

section Relations

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem cm_ar (x y : K) : ⁅xa x, xr y⁆ =
    xu (x * y) * xv (x * y ^ 2) * xb (x * y ^ 3) * xc (x ^ 2 * y ^ 3) :=
  Subtype.ext (rel_ar x y)

theorem cm_ru (x y : K) : ⁅xr x, xu y⁆ = xc (x * y ^ 2) * xb (x ^ 2 * y) :=
  Subtype.ext (rel_ru x y)

theorem cm_rv (x y : K) : ⁅xr x, xv y⁆ = xb (x * y) :=
  Subtype.ext (rel_rv x y)

theorem cm_ab (x y : K) : ⁅xa x, xb y⁆ = xc (x * y) :=
  Subtype.ext (rel_ab x y)

theorem cm_uv (x y : K) : ⁅xu x, xv y⁆ = xc (x * y) :=
  Subtype.ext (rel_uv x y)

theorem cm_vnr (x y : K) : ⁅xv x, xnr y⁆ = xa (x * y ^ 2) * xc (x ^ 2 * y) :=
  Subtype.ext (rel_vnr x y)

theorem cc_au (x y : K) : Commute (xa x) (xu y) :=
  Subtype.ext (comm_au x y).eq

theorem cc_av (x y : K) : Commute (xa x) (xv y) :=
  Subtype.ext (comm_av x y).eq

theorem cc_ac (x y : K) : Commute (xa x) (xc y) :=
  Subtype.ext (comm_ac x y).eq

theorem cc_rb (x y : K) : Commute (xr x) (xb y) :=
  Subtype.ext (comm_rb x y).eq

theorem cc_rc (x y : K) : Commute (xr x) (xc y) :=
  Subtype.ext (comm_rc x y).eq

theorem cc_ub (x y : K) : Commute (xu x) (xb y) :=
  Subtype.ext (comm_ub x y).eq

theorem cc_uc (x y : K) : Commute (xu x) (xc y) :=
  Subtype.ext (comm_uc x y).eq

theorem cc_vb (x y : K) : Commute (xv x) (xb y) :=
  Subtype.ext (comm_vb x y).eq

theorem cc_vc (x y : K) : Commute (xv x) (xc y) :=
  Subtype.ext (comm_vc x y).eq

theorem cc_bc (x y : K) : Commute (xb x) (xc y) :=
  Subtype.ext (comm_bc x y).eq

end Relations

section Tails

variable {G : Type*} [Group G]

theorem tail_of_commute {g h : G} (c : Commute g h) (Z : G) : h * (g * Z) = g * (h * Z) := by
  calc h * (g * Z) = (h * g) * Z := (mul_assoc h g Z).symm
    _ = (g * h) * Z := by rw [c.eq]
    _ = g * (h * Z) := mul_assoc g h Z

theorem tail_of_swap {g h w : G} (hs : h * g = g * h * w) (Z : G) :
    h * (g * Z) = g * (h * (w * Z)) := by
  calc h * (g * Z) = (h * g) * Z := (mul_assoc h g Z).symm
    _ = (g * h * w) * Z := by rw [hs]
    _ = g * (h * (w * Z)) := by simp only [mul_assoc]

theorem swap_of_mul_self {g h : G} (hg : g * g = 1) (hh : h * h = 1) :
    h * g = g * h * ⁅h, g⁆ := by
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hh' : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  rw [commutatorElement_def, hg', hh']
  have e : g * h * (h * g * h * g) = (g * (h * h) * g) * (h * g) := by group
  rw [e, hh, mul_one, hg, one_mul]

theorem conj_of_mul_self {g h : G} (hg : g * g = 1) (hh : h * h = 1) :
    g * h * g = ⁅g, h⁆ * h := by
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hh' : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  rw [commutatorElement_def, hg', hh']
  have e : g * h * g * h * h = g * h * g * (h * h) := by group
  rw [e, hh, mul_one]

end Tails

section TailRules

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem tl_ua (x y : K) (Z : C K) : xu y * (xa x * Z) = xa x * (xu y * Z) :=
  tail_of_commute (cc_au x y) Z

theorem tl_va (x y : K) (Z : C K) : xv y * (xa x * Z) = xa x * (xv y * Z) :=
  tail_of_commute (cc_av x y) Z

theorem tl_ca (x y : K) (Z : C K) : xc y * (xa x * Z) = xa x * (xc y * Z) :=
  tail_of_commute (cc_ac x y) Z

theorem tl_br (x y : K) (Z : C K) : xb y * (xr x * Z) = xr x * (xb y * Z) :=
  tail_of_commute (cc_rb x y) Z

theorem tl_cr (x y : K) (Z : C K) : xc y * (xr x * Z) = xr x * (xc y * Z) :=
  tail_of_commute (cc_rc x y) Z

theorem tl_bu (x y : K) (Z : C K) : xb y * (xu x * Z) = xu x * (xb y * Z) :=
  tail_of_commute (cc_ub x y) Z

theorem tl_cu (x y : K) (Z : C K) : xc y * (xu x * Z) = xu x * (xc y * Z) :=
  tail_of_commute (cc_uc x y) Z

theorem tl_bv (x y : K) (Z : C K) : xb y * (xv x * Z) = xv x * (xb y * Z) :=
  tail_of_commute (cc_vb x y) Z

theorem tl_cv (x y : K) (Z : C K) : xc y * (xv x * Z) = xv x * (xc y * Z) :=
  tail_of_commute (cc_vc x y) Z

theorem tl_cb (x y : K) (Z : C K) : xc y * (xb x * Z) = xb x * (xc y * Z) :=
  tail_of_commute (cc_bc x y) Z

theorem xa_tail_add (x y : K) (Z : C K) : xa x * (xa y * Z) = xa (x + y) * Z := by
  rw [← mul_assoc, ← xa_add]

theorem xr_tail_add (x y : K) (Z : C K) : xr x * (xr y * Z) = xr (x + y) * Z := by
  rw [← mul_assoc, ← xr_add]

theorem xu_tail_add (x y : K) (Z : C K) : xu x * (xu y * Z) = xu (x + y) * Z := by
  rw [← mul_assoc, ← xu_add]

theorem xv_tail_add (x y : K) (Z : C K) : xv x * (xv y * Z) = xv (x + y) * Z := by
  rw [← mul_assoc, ← xv_add]

theorem xb_tail_add (x y : K) (Z : C K) : xb x * (xb y * Z) = xb (x + y) * Z := by
  rw [← mul_assoc, ← xb_add]

theorem xc_tail_add (x y : K) (Z : C K) : xc x * (xc y * Z) = xc (x + y) * Z := by
  rw [← mul_assoc, ← xc_add]

theorem cm_vu (x y : K) : ⁅xv y, xu x⁆ = xc (x * y) := by
  rw [← commutatorElement_inv, cm_uv, xc_inv]

theorem cm_ba (x y : K) : ⁅xb y, xa x⁆ = xc (x * y) := by
  rw [← commutatorElement_inv, cm_ab, xc_inv]

theorem cm_vr (x y : K) : ⁅xv y, xr x⁆ = xb (x * y) := by
  rw [← commutatorElement_inv, cm_rv, xb_inv]

theorem cm_ur (x y : K) : ⁅xu y, xr x⁆ = xb (x ^ 2 * y) * xc (x * y ^ 2) := by
  rw [← commutatorElement_inv, cm_ru, mul_inv_rev, xb_inv, xc_inv]

theorem cm_nrv (x y : K) : ⁅xnr y, xv x⁆ = xa (x * y ^ 2) * xc (x ^ 2 * y) := by
  rw [← commutatorElement_inv, cm_vnr, mul_inv_rev, xa_inv, xc_inv, (cc_ac _ _).eq]

theorem sw_vu (x y : K) : xv y * xu x = xu x * xv y * xc (x * y) := by
  rw [← cm_vu]
  exact swap_of_mul_self (xu_mul_self x) (xv_mul_self y)

theorem tl_vu (x y : K) (Z : C K) :
    xv y * (xu x * Z) = xu x * (xv y * (xc (x * y) * Z)) := by
  rw [tail_of_swap (sw_vu x y) Z]

theorem rev_uvbc (p q s t : K) (Z : C K) :
    xc t * (xb s * (xv q * (xu p * Z))) =
      xu p * (xv q * (xb s * (xc (t + p * q) * Z))) := by
  rw [tl_vu, tl_bu, tl_cu, tl_bv, tl_cv, tl_cb, xc_tail_add]

theorem cm_ra (x y : K) :
    ⁅xr y, xa x⁆ = xu (x * y) * xv (x * y ^ 2) * xb (x * y ^ 3) := by
  rw [← commutatorElement_inv, cm_ar]
  simp only [mul_inv_rev, xu_inv, xv_inv, xb_inv, xc_inv]
  have h := rev_uvbc (x * y) (x * y ^ 2) (x * y ^ 3) (x ^ 2 * y ^ 3) 1
  simp only [mul_one] at h
  have h0 : x ^ 2 * y ^ 3 + x * y * (x * y ^ 2) = 0 := by
    rw [show x * y * (x * y ^ 2) = x ^ 2 * y ^ 3 by ring]
    exact CharTwo.add_self_eq_zero _
  rw [h, h0, xc_zero, mul_one, mul_assoc]

theorem sw_ra (x y : K) :
    xr y * xa x = xa x * xr y * (xu (x * y) * xv (x * y ^ 2) * xb (x * y ^ 3)) := by
  rw [← cm_ra]
  exact swap_of_mul_self (xa_mul_self x) (xr_mul_self y)

theorem sw_ur (x y : K) : xu y * xr x = xr x * xu y * (xb (x ^ 2 * y) * xc (x * y ^ 2)) := by
  rw [← cm_ur]
  exact swap_of_mul_self (xr_mul_self x) (xu_mul_self y)

theorem sw_vr (x y : K) : xv y * xr x = xr x * xv y * xb (x * y) := by
  rw [← cm_vr]
  exact swap_of_mul_self (xr_mul_self x) (xv_mul_self y)

theorem sw_ba (x y : K) : xb y * xa x = xa x * xb y * xc (x * y) := by
  rw [← cm_ba]
  exact swap_of_mul_self (xa_mul_self x) (xb_mul_self y)

theorem tl_ra (x y : K) (Z : C K) :
    xr y * (xa x * Z) =
      xa x * (xr y * (xu (x * y) * (xv (x * y ^ 2) * (xb (x * y ^ 3) * Z)))) := by
  rw [tail_of_swap (sw_ra x y) Z]
  simp only [mul_assoc]

theorem tl_ur (x y : K) (Z : C K) :
    xu y * (xr x * Z) = xr x * (xu y * (xb (x ^ 2 * y) * (xc (x * y ^ 2) * Z))) := by
  rw [tail_of_swap (sw_ur x y) Z]
  simp only [mul_assoc]

theorem tl_vr (x y : K) (Z : C K) :
    xv y * (xr x * Z) = xr x * (xv y * (xb (x * y) * Z)) :=
  tail_of_swap (sw_vr x y) Z

theorem tl_ba (x y : K) (Z : C K) :
    xb y * (xa x * Z) = xa x * (xb y * (xc (x * y) * Z)) :=
  tail_of_swap (sw_ba x y) Z

theorem cj_nrv (x y : K) :
    xnr y * xv x * xnr y = xa (x * y ^ 2) * xc (x ^ 2 * y) * xv x := by
  rw [conj_of_mul_self (xnr_mul_self y) (xv_mul_self x), cm_nrv]

end TailRules

end CFSG.Quasithin.H13.F431.G2
