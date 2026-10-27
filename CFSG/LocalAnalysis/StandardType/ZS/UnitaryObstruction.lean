module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflProductOrder
public import CFSG.LocalAnalysis.StandardType.GGFLWReflForm

public section

namespace CFSG.StandardType.ZS

open Module

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

local instance (priority := high) zuo_zmodAddCommGroup : AddCommGroup (ZMod p) :=
  Ring.toAddCommGroup

private theorem zuo_conj_involution {g : U ≃ₗ[ZMod p] U} (hg : g * g = 1)
    {u : U} {φ : Dual (ZMod p) U} (h : φ u = 2)
    (h' : (φ ∘ₗ (g : U →ₗ[ZMod p] U)) (g u) = 2) :
    g * Module.reflection h * g = Module.reflection h' := by
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Module.reflection_apply,
    Module.reflection_apply, LinearMap.comp_apply]
  have hgg : g (g x) = x := by
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => e x) hg
    simpa [LinearEquiv.mul_apply] using this
  have hsub : g (g x - φ (g x) • u) = g (g x) - g (φ (g x) • u) :=
    AddEquiv.map_sub g.toAddEquiv (g x) (φ (g x) • u)
  rw [hsub, hgg, LinearEquiv.map_smul]
  simp only [LinearEquiv.coe_toLinearMap]

private theorem zuo_normalize {u v : U} {φ ψ : Dual (ZMod p) U}
    (hv : ψ v = 2) (h : φ v * ψ u = 1) :
    ∃ (v' : U) (ψ' : Dual (ZMod p) U) (hv' : ψ' v' = 2),
      Module.reflection hv' = Module.reflection hv ∧ φ v' = -1 ∧ ψ' u = -1 := by
  set c : ZMod p := φ v with hc
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  have hψu : ψ u = c⁻¹ := by
    have h' : c * ψ u = 1 := by rwa [hc]
    exact (inv_eq_of_mul_eq_one_right h').symm
  let t : ZMod p := -c⁻¹
  have ht0 : t ≠ 0 := by
    dsimp only [t]
    exact neg_ne_zero.mpr (inv_ne_zero hc0)
  have htc : t * c = -1 := by
    dsimp only [t]
    field_simp [hc0]
  have htin : t⁻¹ = -c := by
    dsimp only [t]
    field_simp [hc0]
  refine ⟨t • v, t⁻¹ • ψ, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.map_smul ψ t v, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ ht0, one_mul, hv]
  · ext x
    rw [Module.reflection_apply, Module.reflection_apply, LinearMap.smul_apply,
      smul_eq_mul, smul_smul]
    have hcoef : (t⁻¹ * ψ x) * t = ψ x := by
      rw [mul_assoc, mul_comm (ψ x) t, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
    rw [hcoef]
  · rw [LinearMap.map_smul φ t v, smul_eq_mul, ← hc, htc]
  · rw [LinearMap.smul_apply, smul_eq_mul, htin, hψu]
    calc (-c) * c⁻¹ = -(c * c⁻¹) := by ring
      _ = -1 := by rw [mul_inv_cancel₀ hc0]

private theorem zuo_sum_eq_one {x : ZMod p} (hx : x ^ 2 - x + 1 = 0) :
    x + x⁻¹ = 1 := by
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hx
    norm_num at hx
  have h1 : (x ^ 2 - x + 1) * x⁻¹ = 0 := by rw [hx, zero_mul]
  have h2 : (x ^ 2 - x + 1) * x⁻¹ = x + x⁻¹ - 1 := by
    field_simp [hx0]
    ring
  rw [h2] at h1
  exact sub_eq_zero.mp h1

private theorem zuo_quadratic_of_pair {x xin : ZMod p} (hxx : x * xin = 1)
    (h : (xin - 1) * (x - 1) = 1) : x ^ 2 - x + 1 = 0 := by
  have hxin : xin = x⁻¹ := (inv_eq_of_mul_eq_one_right hxx).symm
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hxx
    norm_num at hxx
  rw [hxin] at h
  have h2 : -((x - 1) ^ 2) = x := by
    calc -((x - 1) ^ 2) = x * ((x⁻¹ - 1) * (x - 1)) := by
          field_simp [hx0]
          ring
      _ = x * 1 := by rw [h]
      _ = x := by ring
  linear_combination -h2

private theorem zuo_eq_or_inv_of_quadratic {x y : ZMod p}
    (hx : x ^ 2 - x + 1 = 0) (hy : y ^ 2 - y + 1 = 0) :
    y = x ∨ y = x⁻¹ := by
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hx
    norm_num at hx
  have hxsum : x + x⁻¹ = 1 := zuo_sum_eq_one hx
  have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hprod : (y - x) * (y - x⁻¹) = 0 := by
    calc (y - x) * (y - x⁻¹) = y ^ 2 - (x + x⁻¹) * y + x * x⁻¹ := by ring
      _ = y ^ 2 - y + 1 := by rw [hxsum, hxx]; ring
      _ = 0 := hy
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem zuo_pairing_zero_or_three {x xin y yin : ZMod p}
    (hxx : x * xin = 1) (hyy : y * yin = 1)
    (hx : x ^ 2 - x + 1 = 0) (hy : y ^ 2 - y + 1 = 0) :
    (x - 1 + yin) * (xin - 1 + y) = 0 ∨
      (x - 1 + yin) * (xin - 1 + y) = 3 := by
  have hxin : xin = x⁻¹ := (inv_eq_of_mul_eq_one_right hxx).symm
  have hyin : yin = y⁻¹ := (inv_eq_of_mul_eq_one_right hyy).symm
  have hxsum : x + x⁻¹ = 1 := zuo_sum_eq_one hx
  have hP03 : (x - 1 + yin) * (xin - 1 + y) = 0 ∨
      (x - 1 + yin) * (xin - 1 + y) = 3 := by
    rcases zuo_eq_or_inv_of_quadratic hx hy with hyx | hyinv
    · left
      rw [hyin, hyx, hxin]
      calc (x - 1 + x⁻¹) * (x⁻¹ - 1 + x) = (x + x⁻¹ - 1) ^ 2 := by ring
        _ = 0 := by rw [hxsum]; ring
    · right
      rw [hyin, hyinv, inv_inv, hxin]
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0] at hxx
        norm_num at hxx
      calc (x - 1 + x) * (x⁻¹ - 1 + x⁻¹) = 5 - 2 * (x + x⁻¹) := by
            field_simp [hx0]
            ring
        _ = 3 := by rw [hxsum]; ring
  exact hP03

private theorem zuo_false_of_pairing (hp : p ≠ 2) {x xin y yin : ZMod p}
    (hP : (x - 1 + yin) * (xin - 1 + y) = 1 ∨
      (x - 1 + yin) * (xin - 1 + y) = 4)
    (hP03 : (x - 1 + yin) * (xin - 1 + y) = 0 ∨
      (x - 1 + yin) * (xin - 1 + y) = 3) : False := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h4ne : (4 : ZMod p) ≠ 0 := by
    have h4 : (4 : ZMod p) = 2 * 2 := by ring
    rw [h4]
    exact mul_ne_zero h2 h2
  have h31 : (3 : ZMod p) ≠ 1 := by
    intro h31
    have h2zero : (2 : ZMod p) = 0 := by
      calc (2 : ZMod p) = 3 - 1 := by ring
        _ = 1 - 1 := by rw [h31]
        _ = 0 := by ring
    exact h2 h2zero
  have h34 : (3 : ZMod p) ≠ 4 := by
    intro h34
    have h1zero : (1 : ZMod p) = 0 := by
      calc (1 : ZMod p) = 4 - 3 := by ring
        _ = 4 - 4 := by rw [h34]
        _ = 0 := by ring
    exact one_ne_zero h1zero
  rcases hP03 with hP0 | hP3
  · rcases hP with hP1 | hP4
    · rw [hP0] at hP1
      exact one_ne_zero hP1.symm
    · rw [hP0] at hP4
      exact h4ne hP4.symm
  · rcases hP with hP1 | hP4
    · exact h31 (hP3.symm.trans hP1)
    · exact h34 (hP3.symm.trans hP4)

private structure ZuoData (p : ℕ) [Fact p.Prime] (U : Type) [AddCommGroup U]
    [Module (ZMod p) U] where
  ua : U
  ub : U
  uc : U
  ud : U
  φa : Dual (ZMod p) U
  φb : Dual (ZMod p) U
  φc : Dual (ZMod p) U
  φd : Dual (ZMod p) U
  ha : φa ua = 2
  hb : φb ub = 2
  hc : φc uc = 2
  hd : φd ud = 2
  ub' : U
  φb' : Dual (ZMod p) U
  hb' : φb' ub' = 2
  hrb' : Module.reflection hb' = Module.reflection hb
  hCab' : φa ub' = -1
  hCba' : φb' ua = -1
  uc' : U
  φc' : Dual (ZMod p) U
  hc' : φc' uc' = 2
  hrc' : Module.reflection hc' = Module.reflection hc
  hCac' : φa uc' = -1
  hCca' : φc' ua = -1
  ud' : U
  φd' : Dual (ZMod p) U
  hd' : φd' ud' = 2
  hrd' : Module.reflection hd' = Module.reflection hd
  hCad' : φa ud' = -1
  hCda' : φd' ua = -1
  hbc' : orderOf (Module.reflection hb' * Module.reflection hc') = 3
  hcd' : orderOf (Module.reflection hc' * Module.reflection hd') = 3
  hbd' : orderOf (Module.reflection hb' * Module.reflection hd') = 2
  h5bd' : φb' ud' = 0 ∧ φd' ub' = 0
  h4bc' : φb' uc' * φc' ub' = 1
  h4cd' : φc' ud' * φd' uc' = 1
  hacb' : orderOf ((Module.reflection hc' * Module.reflection ha * Module.reflection hc') *
    Module.reflection hb') = 3
  hacd' : orderOf ((Module.reflection hc' * Module.reflection ha * Module.reflection hc') *
    Module.reflection hd') = 3
  hlast' : orderOf ((Module.reflection hb' * Module.reflection ha * Module.reflection hb') *
      (Module.reflection hd' * Module.reflection hc' * Module.reflection hd')) = 3 ∨
      Module.reflection hb' * Module.reflection ha * Module.reflection hb' =
      Module.reflection hd' * Module.reflection hc' * Module.reflection hd'

private theorem zuo_unitaryFour_data (hp : p ≠ 2) {ua ub uc ud : U}
    {φa φb φc φd : Dual (ZMod p) U}
    (ha : φa ua = 2) (hb : φb ub = 2) (hc : φc uc = 2) (hd : φd ud = 2)
    (hab : orderOf (Module.reflection ha * Module.reflection hb) = 3)
    (hac : orderOf (Module.reflection ha * Module.reflection hc) = 3)
    (had : orderOf (Module.reflection ha * Module.reflection hd) = 3)
    (hbc : orderOf (Module.reflection hb * Module.reflection hc) = 3)
    (hcd : orderOf (Module.reflection hc * Module.reflection hd) = 3)
    (hbd : orderOf (Module.reflection hb * Module.reflection hd) = 2)
    (hacb : orderOf ((Module.reflection hc * Module.reflection ha * Module.reflection hc) *
      Module.reflection hb) = 3)
    (hacd : orderOf ((Module.reflection hc * Module.reflection ha * Module.reflection hc) *
      Module.reflection hd) = 3)
    (hlast : orderOf ((Module.reflection hb * Module.reflection ha * Module.reflection hb) *
      (Module.reflection hd * Module.reflection hc * Module.reflection hd)) = 3 ∨
      Module.reflection hb * Module.reflection ha * Module.reflection hb =
      Module.reflection hd * Module.reflection hc * Module.reflection hd) :
    ∃ _D : ZuoData p U, True := by
  have h4ab : φa ub * φb ua = 1 := mul_eq_one_of_orderOf_eq_three hp ha hb hab
  have h4ac : φa uc * φc ua = 1 := mul_eq_one_of_orderOf_eq_three hp ha hc hac
  have h4ad : φa ud * φd ua = 1 := mul_eq_one_of_orderOf_eq_three hp ha hd had
  have h4bc : φb uc * φc ub = 1 := mul_eq_one_of_orderOf_eq_three hp hb hc hbc
  have h4cd : φc ud * φd uc = 1 := mul_eq_one_of_orderOf_eq_three hp hc hd hcd
  have h5bd : φb ud = 0 ∧ φd ub = 0 := eq_zero_of_orderOf_eq_two hp hb hd hbd
  obtain ⟨ub', φb', hb', hrb', hCab', hCba'⟩ := zuo_normalize hb h4ab
  obtain ⟨uc', φc', hc', hrc', hCac', hCca'⟩ := zuo_normalize hc h4ac
  obtain ⟨ud', φd', hd', hrd', hCad', hCda'⟩ := zuo_normalize hd h4ad
  have hbc' : orderOf (Module.reflection hb' * Module.reflection hc') = 3 := by
    rw [hrb', hrc']
    exact hbc
  have hcd' : orderOf (Module.reflection hc' * Module.reflection hd') = 3 := by
    rw [hrc', hrd']
    exact hcd
  have hbd' : orderOf (Module.reflection hb' * Module.reflection hd') = 2 := by
    rw [hrb', hrd']
    exact hbd
  have h5bd' : φb' ud' = 0 ∧ φd' ub' = 0 :=
    eq_zero_of_orderOf_eq_two hp hb' hd' hbd'
  have h4bc' : φb' uc' * φc' ub' = 1 :=
    mul_eq_one_of_orderOf_eq_three hp hb' hc' hbc'
  have h4cd' : φc' ud' * φd' uc' = 1 :=
    mul_eq_one_of_orderOf_eq_three hp hc' hd' hcd'
  have hacb' : orderOf ((Module.reflection hc' * Module.reflection ha * Module.reflection hc') *
      Module.reflection hb') = 3 := by
    simpa [hrc', hrb'] using hacb
  have hacd' : orderOf ((Module.reflection hc' * Module.reflection ha * Module.reflection hc') *
      Module.reflection hd') = 3 := by
    simpa [hrc', hrd'] using hacd
  have hlast' : orderOf ((Module.reflection hb' * Module.reflection ha * Module.reflection hb') *
      (Module.reflection hd' * Module.reflection hc' * Module.reflection hd')) = 3 ∨
      Module.reflection hb' * Module.reflection ha * Module.reflection hb' =
      Module.reflection hd' * Module.reflection hc' * Module.reflection hd' := by
    simpa [hrb', hrc', hrd'] using hlast
  exact ⟨⟨ua, ub, uc, ud, φa, φb, φc, φd, ha, hb, hc, hd,
    ub', φb', hb', hrb', hCab', hCba',
    uc', φc', hc', hrc', hCac', hCca',
    ud', φd', hd', hrd', hCad', hCda',
    hbc', hcd', hbd', h5bd', h4bc', h4cd', hacb', hacd', hlast'⟩, trivial⟩

private theorem zuo_unitaryFour_ac (D : ZuoData p U) (hp : p ≠ 2) :
    ((D.φa ∘ₗ (Module.reflection D.hc' : U →ₗ[ZMod p] U)) D.ub' *
      D.φb' (Module.reflection D.hc' D.ua) = 1) ∧
    ((D.φa ∘ₗ (Module.reflection D.hc' : U →ₗ[ZMod p] U)) D.ud' *
      D.φd' (Module.reflection D.hc' D.ua) = 1) := by
  rcases D with ⟨ua, ub, uc, ud, φa, φb, φc, φd, ha, hb, hc, hd,
    ub', φb', hb', hrb', hCab', hCba', uc', φc', hc', hrc', hCac', hCca',
    ud', φd', hd', hrd', hCad', hCda', hbc', hcd', hbd', h5bd', h4bc', h4cd',
    hacb', hacd', hlast'⟩
  have h1 : (φa ∘ₗ (Module.reflection hc' : U →ₗ[ZMod p] U))
      (Module.reflection hc' ua) = 2 := by
    rw [LinearMap.comp_apply]
    change φa ((Module.reflection hc') ((Module.reflection hc') ua)) = 2
    have hcc : Module.reflection hc' (Module.reflection hc' ua) = ua := by
      exact Module.involutive_reflection hc' ua
    rw [hcc, ha]
  have hRac : Module.reflection hc' * Module.reflection ha * Module.reflection hc' =
      Module.reflection h1 :=
    zuo_conj_involution (mul_eq_one_iff_eq_inv.mpr (Module.reflection_inv hc').symm) ha h1
  have hord_acb : orderOf (Module.reflection h1 * Module.reflection hb') = 3 := by
    have := hacb'
    rw [hRac] at this
    exact this
  have hord_acd : orderOf (Module.reflection h1 * Module.reflection hd') = 3 := by
    have := hacd'
    rw [hRac] at this
    exact this
  have h4acb : (φa ∘ₗ (Module.reflection hc' : U →ₗ[ZMod p] U)) ub' *
      φb' (Module.reflection hc' ua) = 1 :=
    mul_eq_one_of_orderOf_eq_three hp h1 hb' hord_acb
  have h4acd : (φa ∘ₗ (Module.reflection hc' : U →ₗ[ZMod p] U)) ud' *
      φd' (Module.reflection hc' ua) = 1 :=
    mul_eq_one_of_orderOf_eq_three hp h1 hd' hord_acd
  exact ⟨h4acb, h4acd⟩

private theorem zuo_unitaryFour_xy (D : ZuoData p U)
    (hacb : (D.φa ∘ₗ (Module.reflection D.hc' : U →ₗ[ZMod p] U)) D.ub' *
      D.φb' (Module.reflection D.hc' D.ua) = 1)
    (hacd : (D.φa ∘ₗ (Module.reflection D.hc' : U →ₗ[ZMod p] U)) D.ud' *
      D.φd' (Module.reflection D.hc' D.ua) = 1) :
    ∃ x xin y yin : ZMod p, x = D.φb' D.uc' ∧ xin = D.φc' D.ub' ∧
      y = D.φc' D.ud' ∧ yin = D.φd' D.uc' ∧ x * xin = 1 ∧ y * yin = 1 ∧
      x ^ 2 - x + 1 = 0 ∧ y ^ 2 - y + 1 = 0 := by
  rcases D with ⟨ua, ub, uc, ud, φa, φb, φc, φd, ha, hb, hc, hd,
    ub', φb', hb', hrb', hCab', hCba', uc', φc', hc', hrc', hCac', hCca',
    ud', φd', hd', hrd', hCad', hCda', hbc', hcd', hbd', h5bd', h4bc', h4cd',
    hacb', hacd', hlast'⟩
  set x : ZMod p := φb' uc' with hxdef
  set xin : ZMod p := φc' ub' with hxindef
  set y : ZMod p := φc' ud' with hydef
  set yin : ZMod p := φd' uc' with hyindef
  have hf1 : (φa ∘ₗ (Module.reflection hc' : U →ₗ[ZMod p] U)) ub' = xin - 1 := by
    rw [LinearMap.comp_apply]
    change φa ((Module.reflection hc') ub') = xin - 1
    rw [Module.reflection_apply, LinearMap.map_sub φa ub' (φc' ub' • uc'),
      LinearMap.map_smul φa (φc' ub') uc', smul_eq_mul, hCab', hCac', ← hxindef]
    ring
  have hf2 : φb' (Module.reflection hc' ua) = x - 1 := by
    rw [Module.reflection_apply, LinearMap.map_sub φb' ua (φc' ua • uc'),
      LinearMap.map_smul φb' (φc' ua) uc', smul_eq_mul, hCba', hCca', ← hxdef]
    ring
  have hf1d : (φa ∘ₗ (Module.reflection hc' : U →ₗ[ZMod p] U)) ud' = y - 1 := by
    rw [LinearMap.comp_apply]
    change φa ((Module.reflection hc') ud') = y - 1
    rw [Module.reflection_apply, LinearMap.map_sub φa ud' (φc' ud' • uc'),
      LinearMap.map_smul φa (φc' ud') uc', smul_eq_mul, hCad', hCac', ← hydef]
    ring
  have hf2d : φd' (Module.reflection hc' ua) = yin - 1 := by
    rw [Module.reflection_apply, LinearMap.map_sub φd' ua (φc' ua • uc'),
      LinearMap.map_smul φd' (φc' ua) uc', smul_eq_mul, hCda', hCca', ← hyindef]
    ring
  have hxpair : (xin - 1) * (x - 1) = 1 := by
    rw [← hf1, ← hf2]
    exact hacb
  have hypair : (y - 1) * (yin - 1) = 1 := by
    rw [← hf1d, ← hf2d]
    exact hacd
  have hxx : x * xin = 1 := by
    rw [hxdef, hxindef]
    exact h4bc'
  have hyy : y * yin = 1 := by
    rw [hydef, hyindef]
    exact h4cd'
  have hx : x ^ 2 - x + 1 = 0 := zuo_quadratic_of_pair hxx hxpair
  have hy : y ^ 2 - y + 1 = 0 :=
    zuo_quadratic_of_pair hyy (by rw [mul_comm]; exact hypair)
  exact ⟨x, xin, y, yin, hxdef, hxindef, hydef, hyindef, hxx, hyy, hx, hy⟩

private theorem zuo_unitaryFour_F (D : ZuoData p U) (x xin y yin : ZMod p)
    (hxdef : x = D.φb' D.uc') (hxindef : xin = D.φc' D.ub')
    (hydef : y = D.φc' D.ud') (hyindef : yin = D.φd' D.uc') :
    ((D.φa ∘ₗ (Module.reflection D.hb' : U →ₗ[ZMod p] U))
        (Module.reflection D.hd' D.uc') = x - 1 + yin) ∧
    ((D.φc' ∘ₗ (Module.reflection D.hd' : U →ₗ[ZMod p] U))
        (Module.reflection D.hb' D.ua) = xin - 1 + y) := by
  rcases D with ⟨ua, ub, uc, ud, φa, φb, φc, φd, ha, hb, hc, hd,
    ub', φb', hb', hrb', hCab', hCba', uc', φc', hc', hrc', hCac', hCca',
    ud', φd', hd', hrd', hCad', hCda', hbc', hcd', hbd', h5bd', h4bc', h4cd',
    hacb', hacd', hlast'⟩
  have hF1 : (φa ∘ₗ (Module.reflection hb' : U →ₗ[ZMod p] U))
      (Module.reflection hd' uc') = x - 1 + yin := by
    rw [LinearMap.comp_apply]
    change φa ((Module.reflection hb') ((Module.reflection hd') uc')) = x - 1 + yin
    rw [Module.reflection_apply (y := uc') hd']
    have hrd : (Module.reflection hb') (uc' - φd' uc' • ud') =
        (Module.reflection hb') uc' - φd' uc' • (Module.reflection hb') ud' := by
      have h2 : (Module.reflection hb') (φd' uc' • ud') =
          φd' uc' • (Module.reflection hb') ud' := LinearEquiv.map_smul _ _ _
      simp [h2]
    rw [hrd, Module.reflection_apply, Module.reflection_apply, h5bd'.1, zero_smul, sub_zero,
      LinearMap.map_sub φa (uc' - φb' uc' • ub') (φd' uc' • ud'),
      LinearMap.map_sub φa uc' (φb' uc' • ub'),
      LinearMap.map_smul φa (φb' uc') ub', LinearMap.map_smul φa (φd' uc') ud',
      smul_eq_mul, smul_eq_mul, hCab', hCac', hCad', ← hxdef, ← hyindef]
    ring
  have hF2 : (φc' ∘ₗ (Module.reflection hd' : U →ₗ[ZMod p] U))
      (Module.reflection hb' ua) = xin - 1 + y := by
    rw [LinearMap.comp_apply]
    change φc' ((Module.reflection hd') ((Module.reflection hb') ua)) = xin - 1 + y
    rw [Module.reflection_apply (y := ua) hb']
    have hrd : (Module.reflection hd') (ua - φb' ua • ub') =
        (Module.reflection hd') ua - φb' ua • (Module.reflection hd') ub' := by
      have h2 : (Module.reflection hd') (φb' ua • ub') =
          φb' ua • (Module.reflection hd') ub' := LinearEquiv.map_smul _ _ _
      simp [h2]
    rw [hrd, Module.reflection_apply, Module.reflection_apply, h5bd'.2, zero_smul, sub_zero,
      LinearMap.map_sub φc' (ua - φd' ua • ud') (φb' ua • ub'),
      LinearMap.map_sub φc' ua (φd' ua • ud'),
      LinearMap.map_smul φc' (φd' ua) ud', LinearMap.map_smul φc' (φb' ua) ub',
      smul_eq_mul, smul_eq_mul, hCca', hCda', hCba', ← hxindef, ← hydef]
    ring
  exact ⟨hF1, hF2⟩

private theorem zuo_unitaryFour_hP (D : ZuoData p U) (hp : p ≠ 2)
    (x xin y yin : ZMod p)
    (hF1 : (D.φa ∘ₗ (Module.reflection D.hb' : U →ₗ[ZMod p] U))
        (Module.reflection D.hd' D.uc') = x - 1 + yin)
    (hF2 : (D.φc' ∘ₗ (Module.reflection D.hd' : U →ₗ[ZMod p] U))
        (Module.reflection D.hb' D.ua) = xin - 1 + y) :
    (x - 1 + yin) * (xin - 1 + y) = 1 ∨
      (x - 1 + yin) * (xin - 1 + y) = 4 := by
  rcases D with ⟨ua, ub, uc, ud, φa, φb, φc, φd, ha, hb, hc, hd,
    ub', φb', hb', hrb', hCab', hCba', uc', φc', hc', hrc', hCac', hCca',
    ud', φd', hd', hrd', hCad', hCda', hbc', hcd', hbd', h5bd', h4bc', h4cd',
    hacb', hacd', hlast'⟩
  have h1b : (φa ∘ₗ (Module.reflection hb' : U →ₗ[ZMod p] U))
      (Module.reflection hb' ua) = 2 := by
    rw [LinearMap.comp_apply]
    change φa ((Module.reflection hb') ((Module.reflection hb') ua)) = 2
    have hbb : Module.reflection hb' (Module.reflection hb' ua) = ua := by
      exact Module.involutive_reflection hb' ua
    rw [hbb, ha]
  have hR1 : Module.reflection hb' * Module.reflection ha * Module.reflection hb' =
      Module.reflection h1b :=
    zuo_conj_involution (mul_eq_one_iff_eq_inv.mpr (Module.reflection_inv hb').symm) ha h1b
  have h2c : (φc' ∘ₗ (Module.reflection hd' : U →ₗ[ZMod p] U))
      (Module.reflection hd' uc') = 2 := by
    rw [LinearMap.comp_apply]
    change φc' ((Module.reflection hd') ((Module.reflection hd') uc')) = 2
    have hdd : Module.reflection hd' (Module.reflection hd' uc') = uc' := by
      exact Module.involutive_reflection hd' uc'
    rw [hdd, hc']
  have hR2 : Module.reflection hd' * Module.reflection hc' * Module.reflection hd' =
      Module.reflection h2c :=
    zuo_conj_involution (mul_eq_one_iff_eq_inv.mpr (Module.reflection_inv hd').symm) hc' h2c
  have hP : (x - 1 + yin) * (xin - 1 + y) = 1 ∨
      (x - 1 + yin) * (xin - 1 + y) = 4 := by
    have hP' : (φa ∘ₗ (Module.reflection hb' : U →ₗ[ZMod p] U))
        (Module.reflection hd' uc') *
        (φc' ∘ₗ (Module.reflection hd' : U →ₗ[ZMod p] U))
        (Module.reflection hb' ua) = 1 ∨
        (φa ∘ₗ (Module.reflection hb' : U →ₗ[ZMod p] U))
        (Module.reflection hd' uc') *
        (φc' ∘ₗ (Module.reflection hd' : U →ₗ[ZMod p] U))
        (Module.reflection hb' ua) = 4 := by
      rcases hlast' with hord | heq
      · left
        have hord' : orderOf (Module.reflection h1b * Module.reflection h2c) = 3 := by
          rw [hR1, hR2] at hord
          exact hord
        exact mul_eq_one_of_orderOf_eq_three hp h1b h2c hord'
      · right
        have heq' : Module.reflection h1b = Module.reflection h2c := by
          rw [hR1, hR2] at heq
          exact heq
        exact mul_eq_four_of_reflection_eq h1b h2c heq'
    rw [hF1, hF2] at hP'
    exact hP'
  exact hP

theorem false_of_unitaryFour (hp : p ≠ 2) {ua ub uc ud : U}
    {φa φb φc φd : Dual (ZMod p) U}
    (ha : φa ua = 2) (hb : φb ub = 2) (hc : φc uc = 2) (hd : φd ud = 2)
    (hab : orderOf (Module.reflection ha * Module.reflection hb) = 3)
    (hac : orderOf (Module.reflection ha * Module.reflection hc) = 3)
    (had : orderOf (Module.reflection ha * Module.reflection hd) = 3)
    (hbc : orderOf (Module.reflection hb * Module.reflection hc) = 3)
    (hcd : orderOf (Module.reflection hc * Module.reflection hd) = 3)
    (hbd : orderOf (Module.reflection hb * Module.reflection hd) = 2)
    (hacb : orderOf ((Module.reflection hc * Module.reflection ha * Module.reflection hc) *
      Module.reflection hb) = 3)
    (hacd : orderOf ((Module.reflection hc * Module.reflection ha * Module.reflection hc) *
      Module.reflection hd) = 3)
    (hlast : orderOf ((Module.reflection hb * Module.reflection ha * Module.reflection hb) *
      (Module.reflection hd * Module.reflection hc * Module.reflection hd)) = 3 ∨
      Module.reflection hb * Module.reflection ha * Module.reflection hb =
      Module.reflection hd * Module.reflection hc * Module.reflection hd) : False := by
  obtain ⟨D, -⟩ : ∃ D : ZuoData p U, True :=
    zuo_unitaryFour_data hp ha hb hc hd hab hac had hbc hcd hbd hacb hacd hlast
  obtain ⟨h4acb, h4acd⟩ := zuo_unitaryFour_ac D hp
  obtain ⟨x, xin, y, yin, hxdef, hxindef, hydef, hyindef, hxx, hyy, hx, hy⟩ :=
    zuo_unitaryFour_xy D h4acb h4acd
  obtain ⟨hF1, hF2⟩ := zuo_unitaryFour_F D x xin y yin hxdef hxindef hydef hyindef
  have hP := zuo_unitaryFour_hP D hp x xin y yin hF1 hF2
  have hP03 := zuo_pairing_zero_or_three hxx hyy hx hy
  exact zuo_false_of_pairing hp hP hP03

theorem false_of_unitaryFour_of_isRefl (hp : p ≠ 2) {a b c d : U ≃ₗ[ZMod p] U}
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c) (hd : IsRefl p d)
    (hab : orderOf (a * b) = 3) (hac : orderOf (a * c) = 3)
    (had : orderOf (a * d) = 3) (hbc : orderOf (b * c) = 3)
    (hcd : orderOf (c * d) = 3) (hbd : orderOf (b * d) = 2)
    (hacb : orderOf (c * a * c * b) = 3) (hacd : orderOf (c * a * c * d) = 3)
    (hlast : orderOf (b * a * b * (d * c * d)) = 3 ∨ b * a * b = d * c * d) : False := by
  obtain ⟨ua, φa, -, hφa, haR⟩ := CFSG.StandardType.ggFLW_isRefl_form hp ha
  obtain ⟨ub, φb, -, hφb, hbR⟩ := CFSG.StandardType.ggFLW_isRefl_form hp hb
  obtain ⟨uc, φc, -, hφc, hcR⟩ := CFSG.StandardType.ggFLW_isRefl_form hp hc
  obtain ⟨ud, φd, -, hφd, hdR⟩ := CFSG.StandardType.ggFLW_isRefl_form hp hd
  have haE : a = Module.reflection hφa := LinearEquiv.ext haR
  have hbE : b = Module.reflection hφb := LinearEquiv.ext hbR
  have hcE : c = Module.reflection hφc := LinearEquiv.ext hcR
  have hdE : d = Module.reflection hφd := LinearEquiv.ext hdR
  exact false_of_unitaryFour hp hφa hφb hφc hφd
    (by simpa [haE, hbE] using hab) (by simpa [haE, hcE] using hac)
    (by simpa [haE, hdE] using had) (by simpa [hbE, hcE] using hbc)
    (by simpa [hcE, hdE] using hcd) (by simpa [hbE, hdE] using hbd)
    (by simpa [haE, hbE, hcE] using hacb) (by simpa [haE, hcE, hdE] using hacd)
    (by simpa [haE, hbE, hcE, hdE] using hlast)

end CFSG.StandardType.ZS
