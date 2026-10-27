module

public import CFSG.ClassicalGroups.Orthogonal.RootCenters
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZeroMulti

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
private lemma polarNondegOn_of_isCompl {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {Vp Vm : Submodule K V} (hc : IsCompl Vp Vm)
    (horth : ∀ x ∈ Vp, ∀ y ∈ Vm, polar Q x y = 0) :
    PolarNondegOn Q Vp ∧ PolarNondegOn Q Vm := by
  constructor
  · intro x hx hxW
    apply eq_zero_of_polar_eq_zero hQ
    intro v
    obtain ⟨vp, vm, hsum, -⟩ := Submodule.existsUnique_add_of_isCompl hc v
    rw [← hsum, polar_add_right, hxW (vp : V) vp.2, horth x hx (vm : V) vm.2, add_zero]
  · intro x hx hxW
    apply eq_zero_of_polar_eq_zero hQ
    intro v
    obtain ⟨vp, vm, hsum, -⟩ := Submodule.existsUnique_add_of_isCompl hc v
    rw [← hsum, polar_add_right]
    have h1 : polar Q x (vp : V) = 0 := by
      rw [polar_comm]
      exact horth (vp : V) vp.2 x hx
    have h2 : polar Q x (vm : V) = 0 := hxW (vm : V) vm.2
    rw [h1, h2, add_zero]

omit [Finite K] [FiniteDimensional K V] in
private lemma exists_partner_of_polarNondegOn {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : PolarNondegOn Q W) {x : V} (hxW : x ∈ W) (hx0 : x ≠ 0) (hxQ : Q x = 0) :
    ∃ f ∈ W, Q f = 0 ∧ polar Q x f = 1 := by
  obtain ⟨g, hgW, hg⟩ := hW.exists_polar_ne_zero hxW hx0
  obtain ⟨g', hg'W, hg'⟩ : ∃ g' ∈ W, polar Q x g' = 1 :=
    ⟨(polar Q x g)⁻¹ • g, W.smul_mem _ hgW, by
      rw [polar_smul_right_eq, inv_mul_cancel₀ hg]⟩
  have hxx : polar Q x x = 0 := polar_self_eq_zero hxQ
  refine ⟨g' - Q g' • x, W.sub_mem hg'W (W.smul_mem _ hxW), ?_, ?_⟩
  · rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, map_smul_eq_sq, hxQ,
      polar_neg_right, polar_smul_right_eq, polar_comm Q g' x, hg']
    ring
  · rw [polar_sub_right, polar_smul_right_eq, hxx, hg']
    ring

private lemma exists_singular_polar_ne_zero {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : PolarNondegOn Q W) (h3 : 3 ≤ Module.finrank K W) {y : V} (hyW : y ∈ W)
    (hy0 : y ≠ 0) :
    ∃ x ∈ W, x ≠ 0 ∧ Q x = 0 ∧ polar Q y x ≠ 0 := by
  classical
  have hfin : 2 * 1 < Module.finrank K W := by omega
  obtain ⟨x₀, hx₀0, hx₀Q⟩ :=
    CFSG.FiniteField.exists_ne_zero_forall_eq_zero_of_quadraticForm
      (K := K) (V := ↥W) (r := 1) (fun _ => Q.comp W.subtype) (by simpa using hfin)
  have hx₀W : (x₀ : V) ∈ W := x₀.2
  have hx₀0' : (x₀ : V) ≠ 0 := fun h => hx₀0 (Subtype.ext h)
  have hx₀Q' : Q (x₀ : V) = 0 := by simpa using hx₀Q 0
  obtain ⟨g, hgW, hg⟩ := hW.exists_polar_ne_zero hx₀W hx₀0'
  set h : V := (polar Q (x₀ : V) g)⁻¹ • g with hhdef
  have hhW : h ∈ W := W.smul_mem _ hgW
  have hh : polar Q (x₀ : V) h = 1 := by
    rw [hhdef, polar_smul_right_eq, inv_mul_cancel₀ hg]
  let P : HypPair Q := HypPair.ofPolarEqOne hx₀Q' hh
  have hPe : P.e = (x₀ : V) := rfl
  have hPf : P.f = h - Q h • (x₀ : V) := rfl
  have hPeW : P.e ∈ W := by rw [hPe]; exact hx₀W
  have hPfW : P.f ∈ W := by
    rw [hPf]
    exact W.sub_mem hhW (W.smul_mem _ hx₀W)
  by_contra hcon
  have hcon' : ∀ x ∈ W, Q x = 0 → polar Q y x = 0 := by
    intro x hxW hxQ
    by_contra hxy
    exact hcon ⟨x, hxW, (by rintro rfl; exact hxy (polar_zero_right Q y)), hxQ, hxy⟩
  have hzero : ∀ v ∈ W, polar Q y v = 0 := by
    intro v hv
    have hprojW : P.proj v ∈ W := by
      rw [HypPair.proj]
      exact W.sub_mem (W.sub_mem hv (W.smul_mem _ hPeW)) (W.smul_mem _ hPfW)
    have hprojperp : P.proj v ∈ P.perp := P.proj_mem_perp v
    have hprojpol : polar Q P.e (P.proj v) = 0 ∧ polar Q P.f (P.proj v) = 0 :=
      P.mem_perp.mp hprojperp
    have hsing : Q (P.e + P.proj v - Q (P.proj v) • P.f) = 0 := by
      have h1 : Q (P.e + P.proj v) = Q (P.proj v) := by
        rw [QuadraticMap.map_add Q, P.Q_e, hprojpol.1, zero_add, add_zero]
      have h2 : Q (-(Q (P.proj v) • P.f)) = 0 := by
        rw [QuadraticMap.map_neg, map_smul_eq_sq, P.Q_f, mul_zero]
      have h3 : polar Q (P.e + P.proj v) (-(Q (P.proj v) • P.f)) = -Q (P.proj v) := by
        rw [polar_neg_right, polar_add_left, polar_smul_right_eq, polar_smul_right_eq,
          polar_comm Q (P.proj v) P.f, hprojpol.2, P.polar_ef]
        ring
      rw [sub_eq_add_neg, QuadraticMap.map_add Q, h1, h2, h3]
      ring
    have hmem : P.e + P.proj v - Q (P.proj v) • P.f ∈ W :=
      W.sub_mem (W.add_mem hPeW hprojW) (W.smul_mem _ hPfW)
    have h0 := hcon' _ hmem hsing
    rw [sub_eq_add_neg, polar_add_right, polar_add_right, polar_neg_right,
      polar_smul_right_eq] at h0
    have hBPe : polar Q y P.e = 0 := hcon' P.e hPeW P.Q_e
    have hBPf : polar Q y P.f = 0 := hcon' P.f hPfW P.Q_f
    have hBproj : polar Q y (P.proj v) = 0 := by
      simpa [hBPe, hBPf] using h0
    rw [P.eq_add_proj v, polar_add_right, polar_add_right, polar_smul_right_eq,
      polar_smul_right_eq, hBPe, hBPf, hBproj]
    ring
  exact hy0 (hW y hyW hzero)

omit [Finite K] in
private lemma exists_nonsingular_orth {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : PolarNondegOn Q W) (h3 : 3 ≤ Module.finrank K W) {x : V} (hxW : x ∈ W)
    (hx0 : x ≠ 0) (hxQ : Q x = 0) :
    ∃ w ∈ W, polar Q x w = 0 ∧ Q w ≠ 0 := by
  classical
  obtain ⟨f, hfW, hfQ, hxf⟩ := exists_partner_of_polarNondegOn hW hxW hx0 hxQ
  let P : HypPair Q := HypPair.ofPolarEqOne hxQ hxf
  have hPe : P.e = x := rfl
  have hPf : P.f = f := by rw [HypPair.ofPolarEqOne_f, hfQ, zero_smul, sub_zero]
  have hPeW : P.e ∈ W := by rw [hPe]; exact hxW
  have hPfW : P.f ∈ W := by rw [hPf]; exact hfW
  have hWperp : PolarNondegOn Q (W ⊓ P.perp) := PolarNondegOn.inf_perp hW P hPeW hPfW
  have hne : W ⊓ P.perp ≠ ⊥ := by
    intro hbot
    have hle : W ≤ Submodule.span K ({P.e, P.f} : Set V) := by
      intro v hv
      have hprojW : P.proj v ∈ W := by
        rw [HypPair.proj]
        exact W.sub_mem (W.sub_mem hv (W.smul_mem _ hPeW)) (W.smul_mem _ hPfW)
      have hproj : P.proj v ∈ W ⊓ P.perp := ⟨hprojW, P.proj_mem_perp v⟩
      rw [hbot] at hproj
      have hz : P.proj v = 0 := by simpa using hproj
      rw [P.eq_add_proj v, hz, add_zero]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hfinle := Submodule.finrank_mono hle
    have hspan : Module.finrank K (Submodule.span K ({P.e, P.f} : Set V)) ≤ 2 := by
      have h := finrank_span_finset_le_card (R := K) (s := ({P.e, P.f} : Finset V))
      unfold Set.finrank at h
      rw [Finset.coe_pair] at h
      exact h.trans (Finset.card_le_two (a := P.e) (b := P.f))
    omega
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have huW' : u ∈ W := (Submodule.mem_inf.mp huW).1
  have huPerp : u ∈ P.perp := (Submodule.mem_inf.mp huW).2
  have hxu : polar Q x u = 0 := by simpa [hPe] using (P.mem_perp.mp huPerp).1
  by_cases huQ : Q u ≠ 0
  · exact ⟨u, huW', hxu, huQ⟩
  · push Not at huQ
    obtain ⟨v, hvW, huv⟩ := hWperp.exists_polar_ne_zero huW hu0
    have hvW' : v ∈ W := (Submodule.mem_inf.mp hvW).1
    have hvPerp : v ∈ P.perp := (Submodule.mem_inf.mp hvW).2
    have hxv : polar Q x v = 0 := by simpa [hPe] using (P.mem_perp.mp hvPerp).1
    by_cases hvQ : Q v ≠ 0
    · exact ⟨v, hvW', hxv, hvQ⟩
    · push Not at hvQ
      refine ⟨u + v, W.add_mem huW' hvW', ?_, ?_⟩
      · rw [polar_add_right, hxu, hxv, add_zero]
      · rw [QuadraticMap.map_add Q, huQ, hvQ, zero_add, zero_add]
        exact huv

theorem elementaryGroup_le_of_mixed_root {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {Vp Vm : Submodule K V} (hc : IsCompl Vp Vm)
    (horth : ∀ x ∈ Vp, ∀ y ∈ Vm, polar Q x y = 0) (hp3 : 3 ≤ Module.finrank K Vp)
    (hm3 : 3 ≤ Module.finrank K Vm) {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hHp : ∀ u ∈ Vp, ∀ w ∈ Vp, Q u = 0 → polar Q u w = 0 → eichler Q u w ∈ H)
    (hHm : ∀ u ∈ Vm, ∀ w ∈ Vm, Q u = 0 → polar Q u w = 0 → eichler Q u w ∈ H)
    {e w₀ : V} (he : e ∈ Vp) (he0 : e ≠ 0) (heQ : Q e = 0) (hw : w₀ ∈ Vm) (hw0 : w₀ ≠ 0)
    (hew : ∀ c : K, eichler Q e (c • w₀) ∈ H) : elementaryGroup Q ≤ H := by
  classical
  obtain ⟨hVp, hVm⟩ := polarNondegOn_of_isCompl hQ hc horth
  set Y : Submodule K V :=
    { carrier := {w | w ∈ Vm ∧ ∀ c : K, eichler Q e (c • w) ∈ H}
      zero_mem' := by
        refine ⟨Vm.zero_mem, fun c => ?_⟩
        rw [smul_zero, eichler_zero_right]
        exact H.one_mem
      add_mem' := by
        rintro u v ⟨hu, huH⟩ ⟨hv, hvH⟩
        refine ⟨Vm.add_mem hu hv, fun c => ?_⟩
        have hcu : polar Q e (c • u) = 0 := horth e he (c • u) (Vm.smul_mem _ hu)
        have hcv : polar Q e (c • v) = 0 := horth e he (c • v) (Vm.smul_mem _ hv)
        rw [smul_add, ← eichler_mul hcu hcv]
        exact H.mul_mem (huH c) (hvH c)
      smul_mem' := by
        rintro a w ⟨hw, hwH⟩
        refine ⟨Vm.smul_mem a hw, fun c => ?_⟩
        rw [smul_smul c a w]
        exact hwH (c * a)
      }
  have hw0Y : w₀ ∈ Y := ⟨hw, hew⟩
  have hYinv : ∀ {u z : V}, u ∈ Vm → z ∈ Vm → Q u = 0 → polar Q u z = 0 →
      ∀ {y : V}, y ∈ Y → eichler Q u z y ∈ Y := by
    intro u z hu hz huQ huz y hy
    have hkH : eichler Q u z ∈ H := hHm u hu z hz huQ huz
    have hkO : eichler Q u z ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      eichler_mem_orthogonalGroup Q u z
    refine ⟨?_, fun c => ?_⟩
    · obtain ⟨a : K, b : K, hab⟩ := eichler_apply_eq_add (Q := Q) u z y
      rw [hab]
      exact Vm.add_mem (Vm.add_mem hy.1 (Vm.smul_mem a hz)) (Vm.smul_mem b hu)
    · have hke : eichler Q u z e = e :=
        eichler_apply_of_polar_eq_zero (horth e he u hu) (horth e he z hz)
      have hconj := eichler_conj hkO e (c • y)
      have harg : eichler Q (eichler Q u z e) (eichler Q u z (c • y)) =
          eichler Q e (c • (eichler Q u z y)) := by
        rw [hke, map_smul]
      rw [harg] at hconj
      rw [← hconj]
      exact H.mul_mem (H.mul_mem hkH (hy.2 c)) (H.inv_mem hkH)
  have hY : Y = Vm := by
    refine le_antisymm (fun w hw => hw.1) ?_
    intro v hv
    obtain ⟨x, hxW, hx0, hxQ, hwx⟩ := exists_singular_polar_ne_zero hVm hm3 hw0Y.1 hw0
    obtain ⟨w, hwW, hxw, hwQ⟩ := exists_nonsingular_orth hVm hm3 hxW hx0 hxQ
    have hneg : polar Q x (-w) = 0 := by rw [polar_neg_right, hxw, neg_zero]
    have hFw : eichler Q x w w₀ - w₀ ∈ Y :=
      Y.sub_mem (hYinv hxW hwW hxQ hxw hw0Y) hw0Y
    have hFw' : eichler Q x (-w) w₀ - w₀ ∈ Y :=
      Y.sub_mem (hYinv hxW (Vm.neg_mem hwW) hxQ hneg hw0Y) hw0Y
    have hxY : x ∈ Y := by
      have hsum := Y.add_mem hFw hFw'
      have heq : (eichler Q x w w₀ - w₀) + (eichler Q x (-w) w₀ - w₀) =
          (-2 * Q w * polar Q w₀ x) • x := by
        rw [eichler_apply hxQ hxw, eichler_apply hxQ hneg, polar_neg_right,
          QuadraticMap.map_neg]
        module
      rw [heq] at hsum
      have hcoef : (-2 * Q w * polar Q w₀ x) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hwQ) hwx
      have := Y.smul_mem ((-2 * Q w * polar Q w₀ x)⁻¹) hsum
      rwa [smul_smul, inv_mul_cancel₀ hcoef, one_smul] at this
    have hYperp : ∀ {u : V}, u ∈ Vm → polar Q x u = 0 → u ∈ Y := by
      intro u hu hxu
      have hneg' : polar Q x (-u) = 0 := by rw [polar_neg_right, hxu, neg_zero]
      have hFu : eichler Q x u w₀ - w₀ ∈ Y :=
        Y.sub_mem (hYinv hxW hu hxQ hxu hw0Y) hw0Y
      have hFu' : eichler Q x (-u) w₀ - w₀ ∈ Y :=
        Y.sub_mem (hYinv hxW (Vm.neg_mem hu) hxQ hneg' hw0Y) hw0Y
      have hdiff := Y.sub_mem hFu hFu'
      have heq : (eichler Q x u w₀ - w₀) - (eichler Q x (-u) w₀ - w₀) =
          (2 * polar Q w₀ x) • u - (2 * polar Q w₀ u) • x := by
        rw [eichler_apply hxQ hxu, eichler_apply hxQ hneg', polar_neg_right,
          QuadraticMap.map_neg]
        module
      rw [heq] at hdiff
      have hcoef : (2 * polar Q w₀ x) ≠ 0 := mul_ne_zero h2 hwx
      have hmem : (2 * polar Q w₀ x) • u ∈ Y := by
        have := Y.add_mem hdiff (Y.smul_mem (2 * polar Q w₀ u) hxY)
        simpa [sub_add_cancel] using this
      have := Y.smul_mem ((2 * polar Q w₀ x)⁻¹) hmem
      rwa [smul_smul, inv_mul_cancel₀ hcoef, one_smul] at this
    set a : K := polar Q v x / polar Q w₀ x with ha
    have hperpW : v - a • w₀ ∈ Vm := Vm.sub_mem hv (Vm.smul_mem a hw0Y.1)
    have hperp : polar Q x (v - a • w₀) = 0 := by
      have hvx : polar Q x v = polar Q v x := polar_comm Q x v
      have hxw : polar Q x w₀ = polar Q w₀ x := polar_comm Q x w₀
      rw [polar_sub_right, polar_smul_right_eq, hvx, hxw, ha]
      field_simp
      ring
    have h1 : v - a • w₀ ∈ Y := hYperp hperpW hperp
    have h2 : a • w₀ ∈ Y := Y.smul_mem a hw0Y
    have hsum : (v - a • w₀) + a • w₀ = v := sub_add_cancel _ _
    rw [← hsum]
    exact Y.add_mem h1 h2
  have heRoot : IsRootCenter Q H e := by
    refine ⟨he0, heQ, fun z hz => ?_⟩
    obtain ⟨zp, zm, hsum, -⟩ := Submodule.existsUnique_add_of_isCompl hc z
    have hzm : polar Q e (zm : V) = 0 := horth e he (zm : V) zm.2
    have hzp : polar Q e (zp : V) = 0 := by
      have h := hz
      rw [← hsum, polar_add_right, hzm, add_zero] at h
      exact h
    have hmul : eichler Q e (zp : V) * eichler Q e (zm : V) = eichler Q e z := by
      rw [eichler_mul hzp hzm, hsum]
    rw [← hmul]
    refine H.mul_mem (hHp e he (zp : V) zp.2 heQ hzp) ?_
    have hzmY : (zm : V) ∈ Y := by rw [hY]; exact zm.2
    simpa using hzmY.2 1
  obtain ⟨f, hfVp, hfQ, hef⟩ := exists_partner_of_polarNondegOn hVp he he0 heQ
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hef
    exact zero_ne_one hef
  obtain ⟨z, hzVp, hfz, hzQ⟩ := exists_nonsingular_orth hVp hp3 hfVp hf0 hfQ
  have hgH : eichler Q f z ∈ H := hHp f hfVp z hzVp hfQ hfz
  have hgeRoot : IsRootCenter Q H (eichler Q f z e) := IsRootCenter.map hH heRoot hgH
  have hge : polar Q e (eichler Q f z e) ≠ 0 := by
    have hcalc : polar Q e (eichler Q f z e) = -Q z * (polar Q e f) ^ 2 := by
      rw [eichler_apply hfQ hfz, polar_sub_right, polar_add_right, polar_smul_right_eq,
        polar_smul_right_eq, polar_self_eq_zero heQ]
      ring
    rw [hcalc, hef]
    simpa using (neg_ne_zero.mpr hzQ)
  have hRootH : IsRootCenter Q H ((polar Q e (eichler Q f z e))⁻¹ • (eichler Q f z e)) :=
    hgeRoot.smul (inv_ne_zero hge)
  set h : V := (polar Q e (eichler Q f z e))⁻¹ • (eichler Q f z e) with hh
  have hhpol : polar Q e h = 1 := by
    rw [hh, polar_smul_right_eq, inv_mul_cancel₀ hge]
  let P : HypPair Q := HypPair.ofPolarEqOne heQ hhpol
  have hPe : P.e = e := rfl
  have hPf : P.f = h - Q h • e := rfl
  have hBef : polar Q e P.f = 1 := by
    rw [← hPe]
    exact P.polar_ef
  have hPfRoot : IsRootCenter Q H P.f :=
    IsRootCenter.of_opposite hH heRoot hRootH (by rw [hhpol]; exact one_ne_zero) P.Q_f
      (by rw [hBef]; exact one_ne_zero)
  exact elementaryGroup_le_of_hypPair hQ hH P (by rw [hPe]; exact heRoot) hPfRoot

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter
