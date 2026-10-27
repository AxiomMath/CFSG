module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2s08k10_decomp {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (xv : V)
    (hH : IsCompl H (Submodule.span (ZMod 3) {xv})) (v : V) :
    ∃ h ∈ H, ∃ c : ZMod 3, v = h + c • xv := by
  have hmem : v ∈ H ⊔ Submodule.span (ZMod 3) {xv} := by
    rw [hH.sup_eq_top]
    exact Submodule.mem_top
  rw [Submodule.mem_sup] at hmem
  obtain ⟨h, hh, z, hz, hsum⟩ := hmem
  rw [Submodule.mem_span_singleton] at hz
  obtain ⟨c, hc⟩ := hz
  exact ⟨h, hh, c, by rw [hc]; exact hsum.symm⟩

private lemma ggQ2s08k10_not_mem_H {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (xv : V) (hx : xv ≠ 0)
    (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRH : ∀ a ∈ R, ∀ h ∈ H, a h ∈ H)
    (g : V ≃ₗ[ZMod 3] V) (hgR : g ∈ R) (hgh : g xv ∈ H) : False := by
  have hxvH : xv ∈ H := by
    have h1 : g⁻¹ (g xv) ∈ H := hRH g⁻¹ (R.inv_mem hgR) (g xv) hgh
    simpa using h1
  have hxvbot : xv ∈ (⊥ : Submodule (ZMod 3) V) := by
    rw [← hH.inf_eq_bot, Submodule.mem_inf]
    exact ⟨hxvH, Submodule.mem_span_singleton_self xv⟩
  rw [Submodule.mem_bot] at hxvbot
  exact hx hxvbot

private lemma ggQ2s08k10_C1_or_Cm {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (xv : V) (hx : xv ≠ 0)
    (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRH : ∀ a ∈ R, ∀ h ∈ H, a h ∈ H)
    (g : V ≃ₗ[ZMod 3] V) (hgR : g ∈ R) :
    g xv - xv ∈ H ∨ g xv + xv ∈ H := by
  obtain ⟨h, hh, c, hdec⟩ := ggQ2s08k10_decomp H xv hH (g xv)
  have hc : c = 0 ∨ c = 1 ∨ c = -1 := by
    have h : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = -1 := by decide
    exact h c
  rcases hc with rfl | rfl | rfl
  · exfalso
    apply ggQ2s08k10_not_mem_H H xv hx hH R hRH g hgR
    rw [hdec]
    simpa using hh
  · left
    rw [hdec]
    simpa using hh
  · right
    have hneg : (-1 : ZMod 3) • xv = -xv := neg_one_smul (ZMod 3) xv
    have heq : h + (-1 : ZMod 3) • xv + xv = h := by rw [hneg]; abel
    rw [hdec, heq]
    exact hh

private lemma ggQ2s08k10_C1_eq_one {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (xv : V) (hx : xv ≠ 0)
    (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (hnt : ∀ a ∈ R, ¬ (Module.finrank (ZMod 3)
      (LinearMap.range (a.toLinearMap - LinearMap.id)) = 1 ∧
      ∀ w, a (a w - w) = a w - w))
    (g : V ≃ₗ[ZMod 3] V) (hgR : g ∈ R) (hgH : ∀ h ∈ H, g h = h)
    (h1 : g xv - xv ∈ H) : g = 1 := by
  set b : V := g xv - xv with hbdef
  have hbH : b ∈ H := by rw [hbdef]; exact h1
  set T : V →ₗ[ZMod 3] V := g.toLinearMap - LinearMap.id with hTdef
  have hTH : ∀ h ∈ H, T h = 0 := by
    intro h hh
    simp [hTdef, hgH h hh]
  have hTxv : T xv = b := by
    rw [hTdef, LinearMap.sub_apply, LinearMap.id_apply]
    exact hbdef.symm
  have hstep : ∀ (h : V) (c : ZMod 3), h ∈ H → T (h + c • xv) = c • b := by
    intro h c hh
    rw [map_add, hTH h hh, map_smul, hTxv, zero_add]
  have hTT : T.comp T = 0 := by
    ext v
    obtain ⟨h, hh, c, rfl⟩ := ggQ2s08k10_decomp H xv hH v
    rw [LinearMap.comp_apply, hstep h c hh, map_smul, hTH b hbH, smul_zero,
      LinearMap.zero_apply]
  have hrange : LinearMap.range T = Submodule.span (ZMod 3) {b} := by
    apply le_antisymm
    · rintro y ⟨v, rfl⟩
      obtain ⟨h, hh, c, rfl⟩ := ggQ2s08k10_decomp H xv hH v
      rw [hstep h c hh]
      exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨xv, hTxv⟩
  by_cases hb0 : b = 0
  · refine LinearEquiv.ext fun v => ?_
    obtain ⟨h, hh, c, rfl⟩ := ggQ2s08k10_decomp H xv hH v
    have hgxv : g xv = xv := by
      have h0 : g xv - xv = 0 := by rw [← hbdef]; exact hb0
      exact sub_eq_zero.mp h0
    have hone : (1 : V ≃ₗ[ZMod 3] V) (h + c • xv) = h + c • xv := by simp
    rw [map_add, map_smul, hgH h hh, hgxv, hone]
  · have hfin : Module.finrank (ZMod 3) (LinearMap.range T) = 1 := by
      rw [hrange]
      exact finrank_span_singleton hb0
    have htrans : ∀ w, g (g w - w) = g w - w := by
      intro w
      have hw : T (T w) = 0 := by
        have h2 : (T.comp T) w = 0 := by rw [hTT, LinearMap.zero_apply]
        simpa [LinearMap.comp_apply] using h2
      have h3 : g (g w - w) - (g w - w) = 0 := by
        simpa [hTdef, LinearMap.sub_apply, LinearMap.comp_apply] using hw
      exact sub_eq_zero.mp h3
    exfalso
    exact (hnt g hgR) ⟨by simpa [hTdef] using hfin, htrans⟩

private lemma ggQ2s08k10_Cm_sq {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (xv : V)
    (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (g : V ≃ₗ[ZMod 3] V) (hgH : ∀ h ∈ H, g h = h)
    (hc : g xv + xv ∈ H) : g * g = 1 := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨h, hh, c, rfl⟩ := ggQ2s08k10_decomp H xv hH v
  set b : V := g xv + xv with hbdef
  have hbH : b ∈ H := by rw [hbdef]; exact hc
  have hgxv : g xv = -xv + b := by rw [hbdef]; abel
  have hgb : g b = b := hgH b hbH
  have hone : (1 : V ≃ₗ[ZMod 3] V) (h + c • xv) = h + c • xv := by simp
  rw [LinearEquiv.mul_apply]
  simp only [map_add, map_smul, map_neg, hgH h hh, hgxv, hgb, hone]
  abel

private lemma ggQ2s08k10_uniq {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (xv : V) (hx : xv ≠ 0)
    (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRH : ∀ a ∈ R, ∀ h ∈ H, a h ∈ H)
    (hnt : ∀ a ∈ R, ¬ (Module.finrank (ZMod 3)
      (LinearMap.range (a.toLinearMap - LinearMap.id)) = 1 ∧
      ∀ w, a (a w - w) = a w - w))
    (k1 : V ≃ₗ[ZMod 3] V) (hk1R : k1 ∈ R) (hk1H : ∀ h ∈ H, k1 h = h) (hk1ne : k1 ≠ 1)
    (k2 : V ≃ₗ[ZMod 3] V) (hk2R : k2 ∈ R) (hk2H : ∀ h ∈ H, k2 h = h) (hk2ne : k2 ≠ 1) :
    k1 = k2 := by
  have hc1 : k1 xv + xv ∈ H := by
    rcases ggQ2s08k10_C1_or_Cm H xv hx hH R hRH k1 hk1R with h | h
    · exact absurd (ggQ2s08k10_C1_eq_one H xv hx hH R hnt k1 hk1R hk1H h) hk1ne
    · exact h
  have hc2 : k2 xv + xv ∈ H := by
    rcases ggQ2s08k10_C1_or_Cm H xv hx hH R hRH k2 hk2R with h | h
    · exact absurd (ggQ2s08k10_C1_eq_one H xv hx hH R hnt k2 hk2R hk2H h) hk2ne
    · exact h
  have hk12R : k1 * k2 ∈ R := R.mul_mem hk1R hk2R
  have hk12H : ∀ h ∈ H, (k1 * k2) h = h := by
    intro h hh
    rw [LinearEquiv.mul_apply, hk2H h hh, hk1H h hh]
  have hc12 : (k1 * k2) xv - xv ∈ H := by
    set b1 : V := k1 xv + xv with hb1def
    set b2 : V := k2 xv + xv with hb2def
    have hb1H : b1 ∈ H := by rw [hb1def]; exact hc1
    have hb2H : b2 ∈ H := by rw [hb2def]; exact hc2
    have hk1' : k1 xv = -xv + b1 := by rw [hb1def]; abel
    have hk2' : k2 xv = -xv + b2 := by rw [hb2def]; abel
    have hcalc : (k1 * k2) xv - xv = b2 - b1 := by
      rw [LinearEquiv.mul_apply, hk2', map_add, map_neg, hk1', hk1H b2 hb2H]
      abel
    rw [hcalc]
    exact H.sub_mem hb2H hb1H
  have hmul : k1 * k2 = 1 :=
    ggQ2s08k10_C1_eq_one H xv hx hH R hnt (k1 * k2) hk12R hk12H hc12
  have hk1sq : k1 * k1 = 1 := ggQ2s08k10_Cm_sq H xv hH k1 hk1H hc1
  calc k1 = k1 * 1 := (mul_one k1).symm
    _ = k1 * (k1 * k2) := by rw [hmul]
    _ = (k1 * k1) * k2 := (mul_assoc k1 k1 k2).symm
    _ = 1 * k2 := by rw [hk1sq]
    _ = k2 := one_mul k2

theorem ggQ2s08core_red_kernel_central {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (xv : V) (hx : xv ≠ 0)
      (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRH : ∀ a ∈ R, ∀ h ∈ H, a h ∈ H)
    (hnt : ∀ a ∈ R, ¬
      (Module.finrank (ZMod 3) (LinearMap.range (a.toLinearMap - LinearMap.id)) = 1 ∧
      ∀ w, a (a w - w) = a w - w))
    (k : V ≃ₗ[ZMod 3] V) (hkR : k ∈ R) (hkH : ∀ h ∈ H, k h = h) (a : V ≃ₗ[ZMod 3] V) (haR : a ∈ R) :
    k * a = a * k := by
  by_cases hk1 : k = 1
  · subst hk1
    rw [one_mul, mul_one]
  · have hgR : a * k * a⁻¹ ∈ R := R.mul_mem (R.mul_mem haR hkR) (R.inv_mem haR)
    have hgH : ∀ h ∈ H, (a * k * a⁻¹) h = h := by
      intro h hh
      have h1 : a⁻¹ h ∈ H := hRH a⁻¹ (R.inv_mem haR) h hh
      have h2 : k (a⁻¹ h) = a⁻¹ h := hkH _ h1
      have h3 : a (a⁻¹ h) = h := by simp
      simp only [LinearEquiv.mul_apply, h2, h3]
    have hgne : a * k * a⁻¹ ≠ 1 := by
      intro h
      apply hk1
      have h1 : a * k = a * 1 := by
        have h2 : (a * k * a⁻¹) * a = 1 * a := by rw [h]
        simpa [mul_assoc] using h2
      exact mul_left_cancel h1
    have hthis : a * k * a⁻¹ = k :=
      ggQ2s08k10_uniq H xv hx hH R hRH hnt (a * k * a⁻¹) hgR hgH hgne k hkR hkH hk1
    have hka : a * k = k * a := by
      have h2 : (a * k * a⁻¹) * a = k * a := by rw [hthis]
      simpa [mul_assoc] using h2
    exact hka.symm

theorem ggQ2s08core_red_kernel_stab {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (xv : V) (hx : xv ≠ 0)
      (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (R W : Subgroup (V ≃ₗ[ZMod 3] V)) (hWR : W ≤ R) (hRH : ∀ a ∈ R, ∀ h ∈ H, a h ∈ H)
    (hnt : ∀ a ∈ R, ¬
      (Module.finrank (ZMod 3) (LinearMap.range (a.toLinearMap - LinearMap.id)) = 1 ∧
      ∀ w, a (a w - w) = a w - w))
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (k : V ≃ₗ[ZMod 3] V) (hkR : k ∈ R) (hkH : ∀ h ∈ H, k h = h) :
    ∃ c : ZMod 3, c ≠ 0 ∧ k xv = c • xv := by
  have hfix : ∀ w ∈ W, w (k xv) = k xv := by
    intro w hw
    have hwR : w ∈ R := hWR hw
    have hcomm : w * k = k * w :=
      (ggQ2s08core_red_kernel_central H xv hx hH R hRH hnt k hkR hkH w hwR).symm
    have hwxv : w xv = xv :=
      (hWfix xv).mpr (Submodule.mem_span_singleton_self xv) w hw
    calc w (k xv) = (w * k) xv := by rw [LinearEquiv.mul_apply]
      _ = (k * w) xv := by rw [hcomm]
      _ = k (w xv) := by rw [LinearEquiv.mul_apply]
      _ = k xv := by rw [hwxv]
  have hkfix : k xv ∈ Submodule.span (ZMod 3) {xv} := (hWfix (k xv)).mp hfix
  rw [Submodule.mem_span_singleton] at hkfix
  obtain ⟨c, hc⟩ := hkfix
  refine ⟨c, ?_, hc.symm⟩
  intro hc0
  have hkxv0 : k xv = 0 := by rw [← hc, hc0, zero_smul]
  have : xv = 0 := k.injective (by rw [hkxv0, map_zero])
  exact hx this

end CFSG.StandardType

end
