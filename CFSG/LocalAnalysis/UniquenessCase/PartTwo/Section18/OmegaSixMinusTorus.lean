module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusLevi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped commutatorElement

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] def IsTorusEl (P : HypPair Q) (c : F) (t : Gom Q) : Prop :=
  t.app P.e = c • P.e ∧ t.app P.f = c⁻¹ • P.f ∧ ∀ x ∈ P.perp, t.app x = x

private theorem gom_ext_of_agree_T2J8 {P : HypPair Q} {g h : Gom Q}
    (he : g.app P.e = h.app P.e) (hf : g.app P.f = h.app P.f)
    (hw : ∀ x ∈ P.perp, g.app x = h.app x) : g = h := by
  apply Gom.ext'
  intro x
  have hx : P.proj x ∈ P.perp := P.proj_mem_perp x
  conv_lhs => rw [P.eq_add_proj x]
  rw [Gom.map_add, Gom.map_add, Gom.map_smul, Gom.map_smul, he, hf, hw _ hx]
  conv_rhs => rw [P.eq_add_proj x]
  rw [Gom.map_add, Gom.map_add, Gom.map_smul, Gom.map_smul]

private theorem proj_add_T2J8 (P : HypPair Q) (x y : V) :
    P.proj (x + y) = P.proj x + P.proj y := by
  simp only [HypPair.proj, polar_add_left, add_smul]
  abel

private theorem proj_smul_T2J8 (P : HypPair Q) (a : F) (x : V) :
    P.proj (a • x) = a • P.proj x := by
  simp only [HypPair.proj, polar_smul_left_eq, smul_sub, smul_smul]

private theorem proj_e_T2J8 (P : HypPair Q) : P.proj P.e = 0 := by
  simp [HypPair.proj, P.polar_ee, P.polar_ef]

private theorem proj_f_T2J8 (P : HypPair Q) : P.proj P.f = 0 := by
  simp [HypPair.proj, P.polar_ff, P.polar_fe]

private theorem proj_self_T2J8 (P : HypPair Q) {w : V} (hw : w ∈ P.perp) :
    P.proj w = w := by
  obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp hw
  rw [HypPair.proj, polar_comm Q w P.f, polar_comm Q w P.e, h1, h2, zero_smul, zero_smul,
    sub_zero, sub_zero]

private theorem eigen_proj_eq_zero_T2J8 (P : HypPair Q) {c : F} {t : Gom Q}
    (ht : IsTorusEl P c t) (hc1 : c ≠ 1) {x : V} (hx : t.app x = c • x) :
    P.proj x = 0 := by
  set w : V := P.proj x with hwdef
  have hw : w ∈ P.perp := P.proj_mem_perp x
  have hdecomp : x = polar Q x P.f • P.e + polar Q x P.e • P.f + w := by
    rw [hwdef]
    exact P.eq_add_proj x
  have htx : t.app x = (polar Q x P.f * c) • P.e + (polar Q x P.e * c⁻¹) • P.f + w := by
    conv_lhs => rw [hdecomp]
    rw [Gom.map_add, Gom.map_add, Gom.map_smul, Gom.map_smul, ht.1, ht.2.1,
      ht.2.2 w hw, smul_smul, smul_smul]
  have hproj_t : P.proj (t.app x) = w := by
    rw [htx, proj_add_T2J8, proj_add_T2J8, proj_smul_T2J8, proj_smul_T2J8, proj_e_T2J8,
      proj_f_T2J8, proj_self_T2J8 P hw]
    simp
  have hproj_lin : P.proj (t.app x) = c • P.proj x := by
    rw [hx, proj_smul_T2J8]
  have hw_eq : w = c • w := by
    rw [hwdef, ← hproj_lin, hproj_t, hwdef]
  have h1c : (1 : F) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have h2 : (1 - c) • w = 0 := by
    rw [sub_smul, one_smul, sub_eq_zero]
    exact hw_eq
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h h1c
  · exact h

private theorem eigen_f_coeff_zero_T2J8 (P : HypPair Q) {c : F} {t : Gom Q}
    (ht : IsTorusEl P c t) (hc0 : c ≠ 0) (hcne : c⁻¹ ≠ c) {x : V}
    (hx : t.app x = c • x) : polar Q x P.e = 0 := by
  set b : F := polar Q x P.e with hb
  have hp1 : polar Q (t.app x) P.e = c * b := by
    rw [hx, polar_smul_left_eq, ← hb]
  have hp2 : polar Q (t.app x) P.e = c⁻¹ * b := by
    have hp := Gom.polar_app t x P.e
    rw [ht.1, polar_smul_right_eq, ← hb] at hp
    calc polar Q (t.app x) P.e
        = c⁻¹ * (c * polar Q (t.app x) P.e) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      _ = c⁻¹ * b := by rw [hp]
  have h3 : c * b = c⁻¹ * b := hp1.symm.trans hp2
  have h4 : (c - c⁻¹) * b = 0 := by
    rw [sub_mul, h3, sub_self]
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd (sub_eq_zero.mp h) (Ne.symm hcne)
  · exact h

private theorem mem_span_singleton_of_eigen_T2J8 (P : HypPair Q) {c : F} {t : Gom Q}
    (ht : IsTorusEl P c t) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {x : V}
    (hx : t.app x = c • x) : x ∈ Submodule.span F {P.e} := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc3
  have hcne : c⁻¹ ≠ c := by
    intro h
    have h2 : c ^ 2 = 1 := by
      have hh := congrArg (fun z => z * c) h
      rw [inv_mul_cancel₀ hc0] at hh
      rw [pow_two]
      exact hh.symm
    have h3 : c = 1 := by
      have h4 : c ^ 3 = c := by rw [pow_succ, h2, one_mul]
      rw [h4] at hc3
      exact hc3
    exact hc1 h3
  have hw0 : P.proj x = 0 := eigen_proj_eq_zero_T2J8 P ht hc1 hx
  have hb0 : polar Q x P.e = 0 := eigen_f_coeff_zero_T2J8 P ht hc0 hcne hx
  have hx_eq : x = polar Q x P.f • P.e := by
    conv_lhs => rw [P.eq_add_proj x]
    rw [hw0, hb0, zero_smul, add_zero, add_zero]
  rw [hx_eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem IsTorusEl.unique {P : HypPair Q} {c : F} {t t' : Gom Q} (ht : IsTorusEl P c t)
    (ht' : IsTorusEl P c t') : t = t' :=
  gom_ext_of_agree_T2J8 (ht.1.trans ht'.1.symm) (ht.2.1.trans ht'.2.1.symm)
    (fun x hx => by rw [ht.2.2 x hx, ht'.2.2 x hx])

theorem isTorusEl_one (P : HypPair Q) : IsTorusEl P 1 (1 : Gom Q) :=
  ⟨by rw [Gom.app_one, one_smul], by rw [Gom.app_one, inv_one, one_smul],
    fun x _ => Gom.app_one x⟩

theorem IsTorusEl.mul {P : HypPair Q} {c d : F} {t s : Gom Q} (ht : IsTorusEl P c t)
    (hs : IsTorusEl P d s) : IsTorusEl P (c * d) (t * s) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Gom.app_mul, hs.1, Gom.map_smul, ht.1, smul_smul, mul_comm]
  · rw [Gom.app_mul, hs.2.1, Gom.map_smul, ht.2.1, smul_smul, mul_inv, mul_comm d⁻¹ c⁻¹]
  · intro x hx
    rw [Gom.app_mul, hs.2.2 x hx, ht.2.2 x hx]

theorem IsTorusEl.app_eq_of_orth {P P' : HypPair Q} (h : P.Orth P') {c : F} {t : Gom Q}
    (ht : IsTorusEl P c t) : t.app P'.e = P'.e ∧ t.app P'.f = P'.f :=
  ⟨ht.2.2 P'.e (HypPair.mem_perp.mpr ⟨h.ee, h.fe⟩),
    ht.2.2 P'.f (HypPair.mem_perp.mpr ⟨h.ef, h.ff⟩)⟩

theorem IsTorusEl.comm_of_orth {P P' : HypPair Q} (h : P.Orth P') {c d : F} {t s : Gom Q}
    (ht : IsTorusEl P c t) (hs : IsTorusEl P' d s) : t * s = s * t := by
  obtain ⟨hse, hsf⟩ := hs.app_eq_of_orth h.symm
  have hs_inv_e : s⁻¹.app P.e = P.e := by
    conv_lhs => rw [← hse]
    rw [Gom.app_inv_app]
  have hs_inv_f : s⁻¹.app P.f = P.f := by
    conv_lhs => rw [← hsf]
    rw [Gom.app_inv_app]
  have hs_inv_perp : ∀ x ∈ P.perp, s⁻¹.app x ∈ P.perp := by
    intro x hx
    rw [HypPair.mem_perp] at hx ⊢
    constructor
    · have hh := Gom.polar_app s P.e (s⁻¹.app x)
      rw [hse, Gom.app_app_inv] at hh
      rw [← hh, hx.1]
    · have hh := Gom.polar_app s P.f (s⁻¹.app x)
      rw [hsf, Gom.app_app_inv] at hh
      rw [← hh, hx.2]
  have key : IsTorusEl P c (s * t * s⁻¹) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Gom.app_mul, Gom.app_mul, hs_inv_e, ht.1, Gom.map_smul, hse]
    · rw [Gom.app_mul, Gom.app_mul, hs_inv_f, ht.2.1, Gom.map_smul, hsf]
    · intro x hx
      rw [Gom.app_mul, Gom.app_mul, ht.2.2 _ (hs_inv_perp x hx), Gom.app_app_inv]
  calc t * s = (s * t * s⁻¹) * s := by conv_lhs => rw [IsTorusEl.unique ht key]
    _ = s * t := by group

theorem IsTorusEl.centralizer_zpowers_le_pointStabilizer {P : HypPair Q} {c : F} {t : Gom Q}
    (ht : IsTorusEl P c t) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    Subgroup.centralizer ((Subgroup.zpowers t : Subgroup (Gom Q)) : Set (Gom Q)) ≤
      pointStabilizer Q P.e := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff] at hy
  have hcomm : t * y = y * t := hy t (Subgroup.mem_zpowers t)
  have hx : t.app (y.app P.e) = c • y.app P.e := by
    rw [← Gom.app_mul, hcomm, Gom.app_mul, ht.1, Gom.map_smul]
  rw [mem_pointStabilizer]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    (mem_span_singleton_of_eigen_T2J8 P ht hc3 hc1 hx)
  exact ⟨a, ha.symm⟩

private theorem levi_commute_T2J8 (P : HypPair Q) {c : F} {t : Gom Q}
    (ht : IsTorusEl P c t) {l : Gom Q} (hl : l ∈ leviSub P) : t * l = l * t := by
  obtain ⟨hle, hlf⟩ := app_eq_of_mem_leviSub P hl
  have hfix_plane : ∀ p ∈ Submodule.span F {P.e, P.f}, l.app p = p := by
    intro p hp
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
    rw [Gom.map_add, Gom.map_smul, Gom.map_smul, hle, hlf]
  have hmap_perp : ∀ w ∈ P.perp, l.app w ∈ P.perp := by
    intro w hw
    rw [HypPair.mem_perp] at hw ⊢
    constructor
    · have hh := Gom.polar_app l P.e w
      rw [hle] at hh
      rw [hh, hw.1]
    · have hh := Gom.polar_app l P.f w
      rw [hlf] at hh
      rw [hh, hw.2]
  have hmap_plane : ∀ p ∈ Submodule.span F {P.e, P.f},
      t.app p ∈ Submodule.span F {P.e, P.f} := by
    intro p hp
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
    rw [Gom.map_add, Gom.map_smul, Gom.map_smul, ht.1, ht.2.1, smul_smul, smul_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  apply Gom.ext'
  intro x
  obtain ⟨p, hp, w, hw, rfl⟩ := CFSG.ClassicalGroups.exists_add_eq P.isCompl_perp x
  have hlhs : (t * l).app (p + w) = t.app p + l.app w := by
    rw [Gom.app_mul, Gom.map_add, Gom.map_add, hfix_plane p hp,
      ht.2.2 (l.app w) (hmap_perp w hw)]
  have hrhs : (l * t).app (p + w) = t.app p + l.app w := by
    rw [Gom.app_mul, Gom.map_add, Gom.map_add, ht.2.2 w hw,
      hfix_plane (t.app p) (hmap_plane p hp)]
  rw [hlhs, hrhs]

theorem IsTorusEl.leviSub_le_centralizer_zpowers {P : HypPair Q} {c : F} {t : Gom Q}
    (ht : IsTorusEl P c t) :
    leviSub P ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup (Gom Q)) : Set (Gom Q)) := by
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  change z ∈ Subgroup.zpowers t at hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hcl : Commute t l := levi_commute_T2J8 P ht hl
  exact (hcl.zpow_left k).eq

private theorem Q_smul_pair_T2J8 (P : HypPair Q) (a b : F) :
    Q (a • P.e + b • P.f) = a * b := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, P.Q_e, P.Q_f,
    polar_smul_left_eq, polar_smul_right_eq, P.polar_ef]
  ring

private noncomputable def dLin_T2J8 (ν : F) (P : HypPair Q) : V →ₗ[F] V :=
  LinearMap.id + (ν - 1) • (polarBilin Q P.f).smulRight P.e +
    (ν⁻¹ - 1) • (polarBilin Q P.e).smulRight P.f

private theorem dLin_apply_T2J8 (ν : F) (P : HypPair Q) (x : V) :
    dLin_T2J8 ν P x = x + ((ν - 1) * polar Q P.f x) • P.e +
      ((ν⁻¹ - 1) * polar Q P.e x) • P.f := by
  simp only [dLin_T2J8, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    LinearMap.id_apply, polarBilin_apply_apply, smul_smul]

private theorem dLin_apply_span_T2J8 (ν : F) (P : HypPair Q) (a b : F) :
    dLin_T2J8 ν P (a • P.e + b • P.f) = (ν * a) • P.e + (ν⁻¹ * b) • P.f := by
  rw [dLin_apply_T2J8]
  have h1 : polar Q P.f (a • P.e + b • P.f) = a := by
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ff, P.polar_fe]
    ring
  have h2 : polar Q P.e (a • P.e + b • P.f) = b := by
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ee, P.polar_ef]
    ring
  rw [h1, h2]
  module

private theorem dLin_mem_span_T2J8 (ν : F) (P : HypPair Q) {p : V}
    (hp : p ∈ Submodule.span F {P.e, P.f}) :
    dLin_T2J8 ν P p ∈ Submodule.span F {P.e, P.f} := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
  rw [dLin_apply_span_T2J8]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem dLin_fix_perp_T2J8 (ν : F) (P : HypPair Q) {w : V} (hw : w ∈ P.perp) :
    dLin_T2J8 ν P w = w := by
  rw [dLin_apply_T2J8]
  obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp hw
  rw [h2, h1, mul_zero, mul_zero, zero_smul, zero_smul, add_zero, add_zero]

private theorem dLin_inv_apply_span_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) (a b : F) :
    dLin_T2J8 ν⁻¹ P (dLin_T2J8 ν P (a • P.e + b • P.f)) = a • P.e + b • P.f := by
  rw [dLin_apply_span_T2J8, dLin_apply_span_T2J8]
  have h1 : ν⁻¹ * (ν * a) = a := by rw [← mul_assoc, inv_mul_cancel₀ hν0, one_mul]
  have h2 : (ν⁻¹)⁻¹ * (ν⁻¹ * b) = b := by
    rw [inv_inv, ← mul_assoc, mul_inv_cancel₀ hν0, one_mul]
  rw [h1, h2]

private theorem dLin_inv_comp_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) (x : V) :
    dLin_T2J8 ν⁻¹ P (dLin_T2J8 ν P x) = x := by
  obtain ⟨p, hp, w, hw, rfl⟩ := CFSG.ClassicalGroups.exists_add_eq P.isCompl_perp x
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
  rw [map_add, map_add, dLin_fix_perp_T2J8 ν P hw, dLin_fix_perp_T2J8 ν⁻¹ P hw,
    dLin_inv_apply_span_T2J8 ν hν0 P a b]

private noncomputable def dEquiv_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) : V ≃ₗ[F] V :=
  LinearEquiv.ofLinearMap (dLin_T2J8 ν P) (dLin_T2J8 ν⁻¹ P)
    (LinearMap.ext fun x => by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply, inv_inv] using
        dLin_inv_comp_T2J8 ν⁻¹ (inv_ne_zero hν0) P x)
    (LinearMap.ext fun x => dLin_inv_comp_T2J8 ν hν0 P x)

private theorem dEquiv_e_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) :
    dEquiv_T2J8 ν hν0 P P.e = ν • P.e := by
  change dLin_T2J8 ν P P.e = ν • P.e
  rw [show P.e = (1 : F) • P.e + (0 : F) • P.f by simp, dLin_apply_span_T2J8]
  simp

private theorem dEquiv_f_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) :
    dEquiv_T2J8 ν hν0 P P.f = ν⁻¹ • P.f := by
  change dLin_T2J8 ν P P.f = ν⁻¹ • P.f
  rw [show P.f = (0 : F) • P.e + (1 : F) • P.f by simp, dLin_apply_span_T2J8]
  simp

private theorem dEquiv_perp_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) {w : V}
    (hw : w ∈ P.perp) : dEquiv_T2J8 ν hν0 P w = w := by
  change dLin_T2J8 ν P w = w
  exact dLin_fix_perp_T2J8 ν P hw

private theorem dEquiv_symm_e_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) :
    (dEquiv_T2J8 ν hν0 P)⁻¹ P.e = ν⁻¹ • P.e := by
  change dLin_T2J8 ν⁻¹ P P.e = ν⁻¹ • P.e
  rw [show P.e = (1 : F) • P.e + (0 : F) • P.f by simp, dLin_apply_span_T2J8]
  simp

private theorem dEquiv_symm_f_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) :
    (dEquiv_T2J8 ν hν0 P)⁻¹ P.f = ν • P.f := by
  change dLin_T2J8 ν⁻¹ P P.f = ν • P.f
  rw [show P.f = (0 : F) • P.e + (1 : F) • P.f by simp, dLin_apply_span_T2J8]
  simp

private theorem dEquiv_symm_perp_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) {w : V}
    (hw : w ∈ P.perp) : (dEquiv_T2J8 ν hν0 P)⁻¹ w = w := by
  change dLin_T2J8 ν⁻¹ P w = w
  exact dLin_fix_perp_T2J8 ν⁻¹ P hw

private theorem map_dLin_span_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) {p : V}
    (hp : p ∈ Submodule.span F {P.e, P.f}) : Q (dLin_T2J8 ν P p) = Q p := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
  rw [dLin_apply_span_T2J8, Q_smul_pair_T2J8, Q_smul_pair_T2J8]
  have hcoeff : (ν * a) * (ν⁻¹ * b) = a * b := by
    calc (ν * a) * (ν⁻¹ * b) = (ν * ν⁻¹) * (a * b) := by ring
      _ = 1 * (a * b) := by rw [mul_inv_cancel₀ hν0]
      _ = a * b := one_mul _
  exact hcoeff

private theorem map_eq_of_fixes_perp_span_T2J8 (P : HypPair Q) (g : V →ₗ[F] V)
    (hperp : ∀ w ∈ P.perp, g w = w)
    (hspan : ∀ p ∈ Submodule.span F {P.e, P.f}, g p ∈ Submodule.span F {P.e, P.f})
    (hQspan : ∀ p ∈ Submodule.span F {P.e, P.f}, Q (g p) = Q p) (x : V) :
    Q (g x) = Q x := by
  obtain ⟨p, hp, w, hw, rfl⟩ := CFSG.ClassicalGroups.exists_add_eq P.isCompl_perp x
  rw [map_add, hperp w hw, QuadraticMap.map_add Q, QuadraticMap.map_add Q, hQspan p hp,
    P.polar_eq_zero_of_mem_span_perp (hspan p hp) hw, P.polar_eq_zero_of_mem_span_perp hp hw]

private theorem map_dLin_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) (x : V) :
    Q (dLin_T2J8 ν P x) = Q x :=
  map_eq_of_fixes_perp_span_T2J8 P (dLin_T2J8 ν P) (fun w hw => dLin_fix_perp_T2J8 ν P hw)
    (fun p hp => dLin_mem_span_T2J8 ν P hp) (fun p hp => map_dLin_span_T2J8 ν hν0 P hp) x

private theorem dEquiv_mem_orthogonalGroup_T2J8 (ν : F) (hν0 : ν ≠ 0) (P : HypPair Q) :
    dEquiv_T2J8 ν hν0 P ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  change Q (dLin_T2J8 ν P x) = Q x
  exact map_dLin_T2J8 ν hν0 P x

private noncomputable def swapLin_T2J8 (P : HypPair Q) : V →ₗ[F] V :=
  LinearMap.id + (polarBilin Q P.f - polarBilin Q P.e).smulRight (P.f - P.e)

private theorem swapLin_apply_T2J8 (P : HypPair Q) (x : V) :
    swapLin_T2J8 P x = x + (polar Q P.f x - polar Q P.e x) • (P.f - P.e) := by
  simp only [swapLin_T2J8, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.sub_apply,
    LinearMap.id_apply, polarBilin_apply_apply]

private theorem swapLin_apply_span_T2J8 (P : HypPair Q) (a b : F) :
    swapLin_T2J8 P (a • P.e + b • P.f) = b • P.e + a • P.f := by
  rw [swapLin_apply_T2J8]
  have h1 : polar Q P.f (a • P.e + b • P.f) = a := by
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ff, P.polar_fe]
    ring
  have h2 : polar Q P.e (a • P.e + b • P.f) = b := by
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ee, P.polar_ef]
    ring
  rw [h1, h2]
  module

private theorem swapLin_mem_span_T2J8 (P : HypPair Q) {p : V}
    (hp : p ∈ Submodule.span F {P.e, P.f}) :
    swapLin_T2J8 P p ∈ Submodule.span F {P.e, P.f} := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
  rw [swapLin_apply_span_T2J8]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem swapLin_fix_perp_T2J8 (P : HypPair Q) {w : V} (hw : w ∈ P.perp) :
    swapLin_T2J8 P w = w := by
  rw [swapLin_apply_T2J8]
  obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp hw
  rw [h2, h1, sub_self, zero_smul, add_zero]

private theorem swapLin_comp_self_T2J8 (P : HypPair Q) (x : V) :
    swapLin_T2J8 P (swapLin_T2J8 P x) = x := by
  obtain ⟨p, hp, w, hw, rfl⟩ := CFSG.ClassicalGroups.exists_add_eq P.isCompl_perp x
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
  rw [map_add, map_add, swapLin_fix_perp_T2J8 P hw, swapLin_fix_perp_T2J8 P hw,
    swapLin_apply_span_T2J8, swapLin_apply_span_T2J8]

private noncomputable def swapEquiv_T2J8 (P : HypPair Q) : V ≃ₗ[F] V :=
  LinearEquiv.ofLinearMap (swapLin_T2J8 P) (swapLin_T2J8 P)
    (LinearMap.ext fun x => swapLin_comp_self_T2J8 P x)
    (LinearMap.ext fun x => swapLin_comp_self_T2J8 P x)

private theorem swapEquiv_e_T2J8 (P : HypPair Q) : swapEquiv_T2J8 P P.e = P.f := by
  change swapLin_T2J8 P P.e = P.f
  rw [show P.e = (1 : F) • P.e + (0 : F) • P.f by simp, swapLin_apply_span_T2J8]
  simp

private theorem swapEquiv_f_T2J8 (P : HypPair Q) : swapEquiv_T2J8 P P.f = P.e := by
  change swapLin_T2J8 P P.f = P.e
  rw [show P.f = (0 : F) • P.e + (1 : F) • P.f by simp, swapLin_apply_span_T2J8]
  simp

private theorem swapEquiv_perp_T2J8 (P : HypPair Q) {w : V} (hw : w ∈ P.perp) :
    swapEquiv_T2J8 P w = w := by
  change swapLin_T2J8 P w = w
  exact swapLin_fix_perp_T2J8 P hw

private theorem swapEquiv_symm_T2J8 (P : HypPair Q) :
    (swapEquiv_T2J8 P)⁻¹ = swapEquiv_T2J8 P := rfl

private theorem map_swapLin_span_T2J8 (P : HypPair Q) {p : V}
    (hp : p ∈ Submodule.span F {P.e, P.f}) : Q (swapLin_T2J8 P p) = Q p := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
  rw [swapLin_apply_span_T2J8, Q_smul_pair_T2J8, Q_smul_pair_T2J8]
  ring

private theorem map_swapLin_T2J8 (P : HypPair Q) (x : V) :
    Q (swapLin_T2J8 P x) = Q x :=
  map_eq_of_fixes_perp_span_T2J8 P (swapLin_T2J8 P) (fun w hw => swapLin_fix_perp_T2J8 P hw)
    (fun p hp => swapLin_mem_span_T2J8 P hp) (fun p hp => map_swapLin_span_T2J8 P hp) x

private theorem swapEquiv_mem_orthogonalGroup_T2J8 (P : HypPair Q) :
    swapEquiv_T2J8 P ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  change Q (swapLin_T2J8 P x) = Q x
  exact map_swapLin_T2J8 P x

theorem exists_isTorusEl [Finite F] [CharP F 2]
    (hcomm : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (P : HypPair Q) {c : F} (hc : c ≠ 0) : ∃ t : Gom Q, IsTorusEl P c t := by
  obtain ⟨ν, hν⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hν
    exact hc hν
  let dd : V ≃ₗ[F] V := dEquiv_T2J8 ν hν0 P
  let ss : V ≃ₗ[F] V := swapEquiv_T2J8 P
  have hd : dd ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    dEquiv_mem_orthogonalGroup_T2J8 ν hν0 P
  have hs : ss ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    swapEquiv_mem_orthogonalGroup_T2J8 P
  have hmem : ⁅dd, ss⁆ ∈ elementaryGroup Q := by
    have hh := Subgroup.commutator_mem_commutator hd hs
    rwa [hcomm] at hh
  have hcomm_e : (⁅dd, ss⁆ : V ≃ₗ[F] V) P.e = c • P.e := by
    rw [commutatorElement_def]
    show dd (ss (dd⁻¹ (ss⁻¹ P.e))) = c • P.e
    rw [swapEquiv_symm_T2J8 P, swapEquiv_e_T2J8, dEquiv_symm_f_T2J8 ν hν0 P,
      LinearEquiv.map_smul, swapEquiv_f_T2J8, LinearEquiv.map_smul, dEquiv_e_T2J8 ν hν0 P,
      smul_smul, hν.symm]
  have hcomm_f : (⁅dd, ss⁆ : V ≃ₗ[F] V) P.f = c⁻¹ • P.f := by
    rw [commutatorElement_def]
    show dd (ss (dd⁻¹ (ss⁻¹ P.f))) = c⁻¹ • P.f
    rw [swapEquiv_symm_T2J8 P, swapEquiv_f_T2J8, dEquiv_symm_e_T2J8 ν hν0 P,
      LinearEquiv.map_smul, swapEquiv_e_T2J8, LinearEquiv.map_smul, dEquiv_f_T2J8 ν hν0 P,
      smul_smul]
    congr 1
    rw [hν, mul_inv]
  have hcomm_perp : ∀ x ∈ P.perp, (⁅dd, ss⁆ : V ≃ₗ[F] V) x = x := by
    intro x hx
    rw [commutatorElement_def]
    show dd (ss (dd⁻¹ (ss⁻¹ x))) = x
    rw [swapEquiv_symm_T2J8 P, swapEquiv_perp_T2J8 P hx, dEquiv_symm_perp_T2J8 ν hν0 P hx,
      swapEquiv_perp_T2J8 P hx, dEquiv_perp_T2J8 ν hν0 P hx]
  exact ⟨⟨⁅dd, ss⁆, hmem⟩, hcomm_e, hcomm_f, hcomm_perp⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
