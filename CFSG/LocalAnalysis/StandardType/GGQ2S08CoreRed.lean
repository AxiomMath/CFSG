module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreRedInv
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreRedKer
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreRes
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreAbs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreFull
public import CFSG.LocalAnalysis.StandardType.GGWAutCommon

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private def ggQ2s08k14_res {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (b : ↥H ≃ₗ[ZMod 3] ↥H) (a : V ≃ₗ[ZMod 3] V) : Prop :=
  ∀ h : ↥H, ((b h : ↥H) : V) = a h

private lemma ggQ2s08k14_res_one {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) : ggQ2s08k14_res H 1 1 := by
  intro h
  rfl

private lemma ggQ2s08k14_res_mul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b b' : ↥H ≃ₗ[ZMod 3] ↥H} {a a' : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08k14_res H b a) (hb' : ggQ2s08k14_res H b' a') :
    ggQ2s08k14_res H (b * b') (a * a') := by
  intro h
  calc (((b * b') h : ↥H) : V) = a ((b' h : ↥H) : V) := hb (b' h)
    _ = a (a' h) := by rw [hb' h]
    _ = (a * a') h := rfl

private lemma ggQ2s08k14_res_inv {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b : ↥H ≃ₗ[ZMod 3] ↥H} {a : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08k14_res H b a) : ggQ2s08k14_res H b⁻¹ a⁻¹ := by
  intro h
  apply a.injective
  calc a (((b⁻¹) h : ↥H) : V) = ((b (b⁻¹ h) : ↥H) : V) := (hb (b⁻¹ h)).symm
    _ = (h : V) := by simp
    _ = a (a⁻¹ h) := by simp

private lemma ggQ2s08k14_res_pow {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b : ↥H ≃ₗ[ZMod 3] ↥H} {a : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08k14_res H b a) : ∀ n : ℕ, ggQ2s08k14_res H (b ^ n) (a ^ n) := by
  intro n
  induction n with
  | zero => simpa using ggQ2s08k14_res_one H
  | succ n ih => rw [pow_succ, pow_succ]; exact ggQ2s08k14_res_mul H ih hb

private lemma ggQ2s08k14_res_unique {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b b' : ↥H ≃ₗ[ZMod 3] ↥H} {a : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08k14_res H b a) (hb' : ggQ2s08k14_res H b' a) : b = b' := by
  ext h
  rw [hb h, hb' h]

private lemma ggQ2s08k14_res_eq_one {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b : ↥H ≃ₗ[ZMod 3] ↥H}
    (hb : ggQ2s08k14_res H b 1) : b = 1 :=
  ggQ2s08k14_res_unique H hb (ggQ2s08k14_res_one H)

private lemma ggQ2s08k14_lift_closure_gen {A : Type} [Group A] {B : Type} [Group B]
    (R : A → B → Prop) (hR1 : R 1 1)
    (hRmul : ∀ {a a' : A} {b b' : B}, R a b → R a' b' → R (a * a') (b * b'))
    (hRinv : ∀ {a : A} {b : B}, R a b → R a⁻¹ b⁻¹)
    (G : Set A) (Gbar : Set B)
    (hgen : ∀ x ∈ G, ∃ b ∈ Subgroup.closure Gbar, R x b) :
    ∀ a ∈ Subgroup.closure G, ∃ b ∈ Subgroup.closure Gbar, R a b := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one => exact ⟨1, (Subgroup.closure Gbar).one_mem, hR1⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨bx, hbx, hbxr⟩ := ihx
      obtain ⟨byy, hby, hbyr⟩ := ihy
      exact ⟨bx * byy, (Subgroup.closure Gbar).mul_mem hbx hby, hRmul hbxr hbyr⟩
  | inv x _ ihx =>
      obtain ⟨bx, hbx, hbxr⟩ := ihx
      exact ⟨bx⁻¹, (Subgroup.closure Gbar).inv_mem hbx, hRinv hbxr⟩

private lemma ggQ2s08k14_lift_fwd {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V)
    (G : Set (V ≃ₗ[ZMod 3] V)) (Gbar : Set (↥H ≃ₗ[ZMod 3] ↥H))
    (hgen : ∀ x ∈ G, ∃ b ∈ Subgroup.closure Gbar, ggQ2s08k14_res H b x) :
    ∀ a ∈ Subgroup.closure G, ∃ b ∈ Subgroup.closure Gbar, ggQ2s08k14_res H b a :=
  ggQ2s08k14_lift_closure_gen (A := V ≃ₗ[ZMod 3] V) (B := ↥H ≃ₗ[ZMod 3] ↥H)
    (fun a b => ggQ2s08k14_res H b a) (ggQ2s08k14_res_one H)
    (fun h1 h2 => ggQ2s08k14_res_mul H h1 h2)
    (fun h1 => ggQ2s08k14_res_inv H h1) G Gbar hgen

private lemma ggQ2s08k14_lift_bwd {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V)
    (G : Set (↥H ≃ₗ[ZMod 3] ↥H)) (Gbar : Set (V ≃ₗ[ZMod 3] V))
    (hgen : ∀ x ∈ G, ∃ b ∈ Subgroup.closure Gbar, ggQ2s08k14_res H x b) :
    ∀ a ∈ Subgroup.closure G, ∃ b ∈ Subgroup.closure Gbar, ggQ2s08k14_res H a b :=
  ggQ2s08k14_lift_closure_gen (A := ↥H ≃ₗ[ZMod 3] ↥H) (B := V ≃ₗ[ZMod 3] V)
    (fun b a => ggQ2s08k14_res H b a) (ggQ2s08k14_res_one H)
    (fun h1 h2 => ggQ2s08k14_res_mul H h1 h2)
    (fun h1 => ggQ2s08k14_res_inv H h1) G Gbar hgen

private lemma ggQ2s08k14_neg_sub_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (c : V) : -c - c = c := by
  have h3 : c + c + c = 0 := by
    have h : (3 : ZMod 3) • c = 0 := by
      rw [show (3 : ZMod 3) = 0 by decide, zero_smul (ZMod 3) c]
    rwa [show (3 : ZMod 3) = 2 + 1 by decide, add_smul, two_smul, one_smul] at h
  have hcc : c + c = -c := eq_neg_of_add_eq_zero_left h3
  calc -c - c = -(c + c) := by abel
    _ = -(-c) := by rw [hcc]
    _ = c := neg_neg c

private lemma ggQ2s08k14_neg_ne_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {c : V} (hc : c ≠ 0) : -c ≠ c := by
  intro h
  apply hc
  have h2 : c + c = 0 := by
    nth_rewrite 2 [h.symm]
    exact add_neg_cancel c
  have h2' : (2 : ZMod 3) • c = 0 := by rw [two_smul]; exact h2
  exact (smul_eq_zero.mp h2').resolve_left (by decide : (2 : ZMod 3) ≠ 0)

private lemma ggQ2s08k14_refl_nontrivial_on {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V) (ha : GGLinRefl a)
    (h : ∃ c ∈ H, c ≠ 0 ∧ ∀ v, a v - v ∈ Submodule.span (ZMod 3) {c}) :
    ∃ c ∈ H, a c ≠ c := by
  obtain ⟨h0, hh0H, _, hh0span⟩ := h
  obtain ⟨c, φ, hφ, hc_eq⟩ := (ggLinRefl_iff_isReflLin a).mp ha
  have hc_ne : c ≠ 0 := by
    rintro rfl
    exact (by decide : (2 : ZMod 3) ≠ 0) (by simpa using hφ.symm)
  have hc_span : c ∈ Submodule.span (ZMod 3) {h0} := by
    have hv := hh0span c
    rw [hc_eq, Module.reflection_apply_self] at hv
    convert hv using 1
    exact (ggQ2s08k14_neg_sub_self c).symm
  have hcH : c ∈ H := by
    have hle : Submodule.span (ZMod 3) {h0} ≤ H := by
      rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hh0H
    exact hle hc_span
  exact ⟨c, hcH, by
    rw [hc_eq, Module.reflection_apply_self]
    exact ggQ2s08k14_neg_ne_self hc_ne⟩

private lemma ggQ2s08k14_eq_one_of_fixes {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (xv : V) (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (k : V ≃ₗ[ZMod 3] V) (hkH : ∀ h ∈ H, k h = h) (hkx : k xv = xv) : k = 1 := by
  ext v
  change k v = v
  have hv : v ∈ H ⊔ Submodule.span (ZMod 3) {xv} := by
    rw [hH.codisjoint.eq_top]
    trivial
  obtain ⟨h, hh, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_add, map_smul, hkH h hh, hkx]

theorem ggQ2s08_core_red (hKG : GGReflClassLargeThree) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V]
    {ℓ : ℕ} (hℓ : 9 ≤ ℓ) (hdim : Module.finrank (ZMod 3) V = ℓ + 1)
    (H : Submodule (ZMod 3) V) (xv : V) (hx : xv ≠ 0)
      (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (R W : Subgroup (V ≃ₗ[ZMod 3] V)) (hWR : W ≤ R) (hWH : ∀ w ∈ W, ∀ h ∈ H, w h ∈ H)
    (s : Fin ℓ → (V ≃ₗ[ZMod 3] V)) (M : CoxeterMatrix (Fin ℓ))
    (hM : M = CoxeterMatrix.A ℓ ∨ M = CoxeterMatrix.B ℓ ∨ M = ggCoxeterMatrixD ℓ)
    (hsrefl : ∀ i, GGLinRefl (s i)) (hsH : ∀ i, ∃ h ∈ H, h ≠ 0 ∧ ∀ v, s i v - v ∈ Submodule.span
      (ZMod 3) {h})
    (hrel : ∀ i j, i ≠ j → (s i * s j) ^ M i j = 1) (hdist : ∀ i j, i ≠ j → s i ≠ s j)
    (hncomm : ∀ i j, i ≠ j → M i j ≠ 2 → s i * s j ≠ s j * s i)
    (hWs : W = Subgroup.closure (Set.range s))
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (hWirrH : ∀ U : Submodule (ZMod 3) V, U ≤ H → (∀ w ∈ W, ∀ u ∈ U, w u ∈ U) → U = ⊥ ∨ U = H)
    (r t : V ≃ₗ[ZMod 3] V) (hR : R = Subgroup.closure ((W : Set (V ≃ₗ[ZMod 3] V)) ∪ {r, t}))
    (hr : GGLinRefl r) (ht : GGLinRefl t) (hrx : ¬ ∃ c : ZMod 3, r xv = c • xv)
    (htx : ¬ ∃ c : ZMod 3, t xv = c • xv)
    (hnt : ∀ a ∈ R, ¬
      (Module.finrank (ZMod 3) (LinearMap.range (a.toLinearMap - LinearMap.id)) = 1 ∧
      ∀ w, a (a w - w) = a w - w))
    (hsmall : 8 * Nat.card R < 3 ^ (ℓ * (ℓ - 1) / 2))
    (hred : ∃ U : Submodule (ZMod 3) V, U ≠ ⊥ ∧ U ≠ ⊤ ∧ ∀ a ∈ R, ∀ u ∈ U, a u ∈ U) :
    t ∈ GGQ2S08M0 R W r xv := by
  classical
  haveI : FiniteDimensional (ZMod 3) V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨U, hU0, hU1, hUR⟩ := hred
  have hrR : r ∈ R := by rw [hR]; exact Subgroup.subset_closure (by simp)
  have htR : t ∈ R := by rw [hR]; exact Subgroup.subset_closure (by simp)
  have hUH : U = H :=
    ggQ2s08core_red_invariant H xv hH W R hWR hWH hWfix hWirrH r hrR hrx U hU0 hU1 hUR
  have hRH : ∀ a ∈ R, ∀ h ∈ H, a h ∈ H := by
    intro a ha h hh
    rw [← hUH]
    exact hUR a ha h (by rw [hUH]; exact hh)
  let Rb : Subgroup (↥H ≃ₗ[ZMod 3] ↥H) := GGQ2S08Res H R hRH
  let Wb : Subgroup (↥H ≃ₗ[ZMod 3] ↥H) := GGQ2S08Res H W hWH
  have hWbR : Wb ≤ Rb := by
    intro b hb
    obtain ⟨a, haW, ha⟩ := hb
    exact ⟨a, hWR haW, ha⟩
  have hWfix_xv : ∀ w ∈ W, w xv = xv :=
    (hWfix xv).mpr (Submodule.mem_span_singleton_self xv)
  have hrHne : ∃ h ∈ H, r h ≠ h := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, _, hcx⟩ :=
      ggQ2s08core_red_kernel_stab H xv hx hH R W hWR hRH hnt hWfix r hrR hcon
    exact hrx ⟨c, hcx⟩
  have htHne : ∃ h ∈ H, t h ≠ h := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, _, hcx⟩ :=
      ggQ2s08core_red_kernel_stab H xv hx hH R W hWR hRH hnt hWfix t htR hcon
    exact htx ⟨c, hcx⟩
  obtain ⟨rbar, hrbarR, hrbar_apply, hrbar_refl⟩ :=
    ggQ2s08core_res_refl H R hRH r hrR hr hrHne
  obtain ⟨tbar, htbarR, htbar_apply, htbar_refl⟩ :=
    ggQ2s08core_res_refl H R hRH t htR ht htHne
  have hsW : ∀ i, s i ∈ W := fun i => by
    rw [hWs]; exact Subgroup.subset_closure ⟨i, rfl⟩
  have hsR : ∀ i, s i ∈ R := fun i => hWR (hsW i)
  have hsHne : ∀ i, ∃ h ∈ H, s i h ≠ h := fun i =>
    ggQ2s08k14_refl_nontrivial_on H (s i) (hsrefl i) (hsH i)
  let sbar : Fin ℓ → (↥H ≃ₗ[ZMod 3] ↥H) := fun i =>
    Classical.choose (ggQ2s08core_res_refl H R hRH (s i) (hsR i) (hsrefl i) (hsHne i))
  have hsbar_spec : ∀ i, (∀ h : ↥H, (((sbar i) h : ↥H) : V) = s i h) ∧ GGLinRefl (sbar i) :=
    fun i => (Classical.choose_spec
      (ggQ2s08core_res_refl H R hRH (s i) (hsR i) (hsrefl i) (hsHne i))).2
  have hsbar_apply : ∀ i, ggQ2s08k14_res H (sbar i) (s i) := fun i => (hsbar_spec i).1
  have hsbar_refl : ∀ i, GGLinRefl (sbar i) := fun i => (hsbar_spec i).2
  have hsbar_mem : ∀ i, sbar i ∈ Rb := fun i => ⟨s i, hsR i, hsbar_apply i⟩
  have hsbarW : ∀ i, sbar i ∈ Wb := fun i => ⟨s i, hsW i, hsbar_apply i⟩
  have hR' : R = Subgroup.closure (Set.range s ∪ ({r, t} : Set (V ≃ₗ[ZMod 3] V))) := by
    rw [hR, hWs]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact Subgroup.closure_mono (Set.subset_union_left) hx
      · exact Subgroup.subset_closure (Set.mem_union_right _ hx)
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact Subgroup.subset_closure (Or.inl (Subgroup.subset_closure hx))
      · exact Subgroup.subset_closure (Or.inr hx)
  have hWb_closure : Wb = Subgroup.closure (Set.range sbar) := by
    apply le_antisymm
    · intro b hb
      obtain ⟨a, haW, ha⟩ := hb
      have haW' : a ∈ Subgroup.closure (Set.range s) := by rwa [hWs] at haW
      have hgen : ∀ x ∈ Set.range s,
          ∃ b ∈ Subgroup.closure (Set.range sbar), ggQ2s08k14_res H b x := by
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        exact ⟨sbar i, Subgroup.subset_closure ⟨i, rfl⟩, hsbar_apply i⟩
      obtain ⟨b', hb', hb'r⟩ := ggQ2s08k14_lift_fwd H (Set.range s) (Set.range sbar) hgen a haW'
      have hbb' : b = b' := ggQ2s08k14_res_unique H ha hb'r
      rwa [hbb']
    · rw [Subgroup.closure_le]
      intro b hb
      obtain ⟨i, rfl⟩ := hb
      exact hsbarW i
  have hgen_fwd : ∀ x ∈ Set.range s ∪ ({r, t} : Set (V ≃ₗ[ZMod 3] V)),
      ∃ b ∈ Subgroup.closure (Set.range sbar ∪ ({rbar, tbar} : Set (↥H ≃ₗ[ZMod 3] ↥H))),
        ggQ2s08k14_res H b x := by
    intro x hx
    rcases hx with ⟨i, rfl⟩ | hx
    · exact ⟨sbar i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩), hsbar_apply i⟩
    · rcases hx with rfl | rfl
      · exact ⟨rbar, Subgroup.subset_closure (Or.inr (by simp)), hrbar_apply⟩
      · exact ⟨tbar, Subgroup.subset_closure (Or.inr (by simp)), htbar_apply⟩
  have hRb_closure :
      Rb = Subgroup.closure (Set.range sbar ∪ ({rbar, tbar} : Set (↥H ≃ₗ[ZMod 3] ↥H))) := by
    apply le_antisymm
    · intro b hb
      obtain ⟨a, haR, ha⟩ := hb
      have haR' : a ∈ Subgroup.closure (Set.range s ∪ ({r, t} : Set (V ≃ₗ[ZMod 3] V))) := hR' ▸ haR
      obtain ⟨b', hb', hb'r⟩ := ggQ2s08k14_lift_fwd H _ _ hgen_fwd a haR'
      have hbb' : b = b' := ggQ2s08k14_res_unique H ha hb'r
      rwa [hbb']
    · rw [Subgroup.closure_le]
      rintro b (hb | hb)
      · obtain ⟨i, rfl⟩ := hb; exact hsbar_mem i
      · rcases hb with rfl | rfl
        · exact hrbarR
        · exact htbarR
  have hgen_refl : Rb = Subgroup.closure {a : ↥H ≃ₗ[ZMod 3] ↥H | a ∈ Rb ∧ GGLinRefl a} := by
    apply le_antisymm
    · calc Rb = Subgroup.closure (Set.range sbar ∪ ({rbar, tbar} : Set (↥H ≃ₗ[ZMod 3] ↥H))) :=
          hRb_closure
        _ ≤ Subgroup.closure {a : ↥H ≃ₗ[ZMod 3] ↥H | a ∈ Rb ∧ GGLinRefl a} := by
          apply Subgroup.closure_mono
          rintro b (hb | hb)
          · obtain ⟨i, rfl⟩ := hb
            exact ⟨hsbar_mem i, hsbar_refl i⟩
          · rcases hb with rfl | rfl
            · exact ⟨hrbarR, hrbar_refl⟩
            · exact ⟨htbarR, htbar_refl⟩
    · rw [Subgroup.closure_le]
      rintro b ⟨hb, _⟩
      exact hb
  have hWirrWb : ZS.AbsIrred 3 Wb := by
    refine ggQ2s08core_absIrred_of_irred Wb ?_ ?_ ?_
    · apply le_antisymm
      · calc Wb = Subgroup.closure (Set.range sbar) := hWb_closure
          _ ≤ Subgroup.closure {a : ↥H ≃ₗ[ZMod 3] ↥H | a ∈ Wb ∧ GGLinRefl a} := by
            apply Subgroup.closure_mono
            rintro b ⟨i, rfl⟩
            exact ⟨hsbarW i, hsbar_refl i⟩
      · rw [Subgroup.closure_le]
        rintro b ⟨hb, _⟩
        exact hb
    · exact ⟨sbar ⟨0, by omega⟩, hsbarW _, hsbar_refl _⟩
    · intro S hS
      have hUle : S.map H.subtype ≤ H := by
        rintro y ⟨x, _, rfl⟩
        exact x.2
      have hWinv : ∀ w ∈ W, ∀ u ∈ S.map H.subtype, w u ∈ S.map H.subtype := by
        intro w hw u hu
        obtain ⟨sq, hsq, rfl⟩ := hu
        obtain ⟨wb, hwbW, hwb_apply⟩ := ggQ2s08core_res_mem H W hWH w hw
        exact ⟨wb sq, hS wb hwbW sq hsq, hwb_apply sq⟩
      rcases hWirrH (S.map H.subtype) hUle hWinv with h | h
      · left
        rw [Submodule.eq_bot_iff]
        intro x hx
        have hx' : (x : V) ∈ S.map H.subtype := ⟨x, hx, rfl⟩
        rw [h] at hx'
        exact Subtype.ext (by simpa using hx')
      · right
        have h' : S.map H.subtype = (⊤ : Submodule (ZMod 3) ↥H).map H.subtype := by
          rw [h, Submodule.map_top, Submodule.range_subtype]
        exact Submodule.map_injective_of_injective H.injective_subtype h'
  have hAbsRb : ZS.AbsIrred 3 Rb := ggWAut_absIrred_of_le hWbR hWirrWb
  haveI : Fintype V := Module.fintypeOfFintype (Module.Basis.ofVectorSpace (ZMod 3) V)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e1 e2 h => LinearEquiv.ext (fun v => congrFun h v))
  have hcard : Nat.card Rb ≤ Nat.card R := by
    classical
    let f : ↥R → ↥Rb := fun a =>
      ⟨Classical.choose (ggQ2s08core_res_mem H R hRH a.1 a.2),
        (Classical.choose_spec (ggQ2s08core_res_mem H R hRH a.1 a.2)).1⟩
    have hf : Function.Surjective f := by
      intro b
      obtain ⟨a, haR, ha⟩ := b.2
      refine ⟨⟨a, haR⟩, ?_⟩
      apply Subtype.ext
      exact ggQ2s08k14_res_unique H
        (Classical.choose_spec (ggQ2s08core_res_mem H R hRH a haR)).2 ha
    exact Nat.card_le_card_of_surjective f hf
  have hsmall_red : 8 * Nat.card Rb < 3 ^ (ℓ * (ℓ - 1) / 2) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 8 hcard) hsmall
  have hdimH : Module.finrank (ZMod 3) ↥H = ℓ := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hH
    rw [hdim] at hsum
    have hL : Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3) {xv}) = 1 := by
      rw [finrank_span_singleton hx]
    rw [hL] at hsum
    omega
  have hrel' : ∀ i j, i ≠ j → (sbar i * sbar j) ^ M i j = 1 := by
    intro i j hij
    have hbase : ggQ2s08k14_res H (sbar i * sbar j) (s i * s j) :=
      ggQ2s08k14_res_mul H (hsbar_apply i) (hsbar_apply j)
    have hpow := ggQ2s08k14_res_pow H hbase (M i j)
    rw [hrel i j hij] at hpow
    exact ggQ2s08k14_res_eq_one H hpow
  have hdist' : ∀ i j, i ≠ j → sbar i ≠ sbar j := by
    intro i j hij heq
    set k : V ≃ₗ[ZMod 3] V := s i * (s j)⁻¹ with hkdef
    have hres : ggQ2s08k14_res H (sbar i * (sbar j)⁻¹) k := by
      rw [hkdef]
      exact ggQ2s08k14_res_mul H (hsbar_apply i) (ggQ2s08k14_res_inv H (hsbar_apply j))
    have hone : sbar i * (sbar j)⁻¹ = 1 := by rw [heq, mul_inv_cancel]
    have hkH : ∀ h ∈ H, k h = h := by
      intro h hh
      have := hres ⟨h, hh⟩
      rw [hone] at this
      simpa using this.symm
    have hkR : k ∈ R := by
      rw [hkdef]
      exact Subgroup.mul_mem _ (hsR i) (Subgroup.inv_mem _ (hsR j))
    obtain ⟨c, _, hcx⟩ :=
      ggQ2s08core_red_kernel_stab H xv hx hH R W hWR hRH hnt hWfix k hkR hkH
    have hsjinv : (s j)⁻¹ xv = xv := by
      have h := (s j).symm_apply_apply xv
      rw [hWfix_xv (s j) (hsW j)] at h
      exact h
    have hkx : k xv = xv := by
      rw [hkdef, LinearEquiv.mul_apply, hsjinv, hWfix_xv (s i) (hsW i)]
    have hc1 : c = 1 := by
      have hcx' : c • xv = (1 : ZMod 3) • xv := by
        rw [one_smul (ZMod 3) xv]
        exact hcx.symm.trans hkx
      have hsub : (c - 1) • xv = 0 := by rw [sub_smul, hcx', sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hx)
    have hk_one : k = 1 := ggQ2s08k14_eq_one_of_fixes H xv hH k hkH hkx
    have hsij : s i = s j := by
      have hk1 : s i * (s j)⁻¹ = 1 := by rw [← hkdef]; exact hk_one
      calc s i = s i * (s j)⁻¹ * s j := by group
        _ = 1 * s j := by rw [hk1]
        _ = s j := one_mul _
    exact (hdist i j hij) hsij
  have hncomm' : ∀ i j, i ≠ j → M i j ≠ 2 → sbar i * sbar j ≠ sbar j * sbar i := by
    intro i j hij hMij heq
    set k : V ≃ₗ[ZMod 3] V := s i * s j * (s j * s i)⁻¹ with hkdef
    have hres : ggQ2s08k14_res H (sbar i * sbar j * (sbar j * sbar i)⁻¹) k := by
      rw [hkdef]
      exact ggQ2s08k14_res_mul H
        (ggQ2s08k14_res_mul H (hsbar_apply i) (hsbar_apply j))
        (ggQ2s08k14_res_inv H (ggQ2s08k14_res_mul H (hsbar_apply j) (hsbar_apply i)))
    have hone : sbar i * sbar j * (sbar j * sbar i)⁻¹ = 1 := by rw [heq, mul_inv_cancel]
    have hkH : ∀ h ∈ H, k h = h := by
      intro h hh
      have := hres ⟨h, hh⟩
      rw [hone] at this
      simpa using this.symm
    have hkR : k ∈ R := by
      rw [hkdef]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsR i) (hsR j))
        (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hsR j) (hsR i)))
    obtain ⟨c, _, hcx⟩ :=
      ggQ2s08core_red_kernel_stab H xv hx hH R W hWR hRH hnt hWfix k hkR hkH
    have hprodinv : (s j * s i)⁻¹ xv = xv := by
      have h := (s j * s i).symm_apply_apply xv
      rw [LinearEquiv.mul_apply, hWfix_xv (s i) (hsW i), hWfix_xv (s j) (hsW j)] at h
      exact h
    have hkx : k xv = xv := by
      rw [hkdef, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hprodinv,
        hWfix_xv (s j) (hsW j), hWfix_xv (s i) (hsW i)]
    have hc1 : c = 1 := by
      have hcx' : c • xv = (1 : ZMod 3) • xv := by
        rw [one_smul (ZMod 3) xv]
        exact hcx.symm.trans hkx
      have hsub : (c - 1) • xv = 0 := by rw [sub_smul, hcx', sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hx)
    have hk_one : k = 1 := ggQ2s08k14_eq_one_of_fixes H xv hH k hkH hkx
    have hcomm : s i * s j = s j * s i := by
      have hk1 : s i * s j * (s j * s i)⁻¹ = 1 := by rw [← hkdef]; exact hk_one
      calc s i * s j = s i * s j * (s j * s i)⁻¹ * (s j * s i) := by group
        _ = 1 * (s j * s i) := by rw [hk1]
        _ = s j * s i := one_mul _
    exact (hncomm i j hij hMij) hcomm
  have hrbarW : rbar ∉ Wb := by
    intro hrbW
    obtain ⟨w, hwW, hw_apply⟩ := hrbW
    set k : V ≃ₗ[ZMod 3] V := r * w⁻¹ with hkdef
    have hkH : ∀ h ∈ H, k h = h := by
      intro h hh
      rw [hkdef, LinearEquiv.mul_apply]
      have hwh : w⁻¹ h ∈ H := hRH w⁻¹ (hWR (W.inv_mem hwW)) h hh
      have h1 : r (w⁻¹ h) = w (w⁻¹ h) := by
        simpa only [Subtype.coe_mk] using
          (hrbar_apply ⟨w⁻¹ h, hwh⟩).symm.trans (hw_apply ⟨w⁻¹ h, hwh⟩)
      rw [h1]
      simpa using LinearEquiv.apply_symm_apply w (h : V)
    have hkR : k ∈ R := by
      rw [hkdef]
      exact Subgroup.mul_mem _ hrR (Subgroup.inv_mem _ (hWR hwW))
    obtain ⟨c, _, hcx⟩ :=
      ggQ2s08core_red_kernel_stab H xv hx hH R W hWR hRH hnt hWfix k hkR hkH
    have hwinv : w⁻¹ xv = xv := by
      have h := w.symm_apply_apply xv
      rw [hWfix_xv w hwW] at h
      exact h
    have hkx : k xv = r xv := by
      rw [hkdef, LinearEquiv.mul_apply, hwinv]
    exact hrx ⟨c, hkx ▸ hcx⟩
  have hfull : Subgroup.closure ((Wb : Set (↥H ≃ₗ[ZMod 3] ↥H)) ∪ {rbar}) = Rb :=
    ggQ2s08core_full_rank hKG hℓ hdimH Rb Wb hAbsRb hgen_refl hsmall_red hWbR hWirrWb
      sbar M hM hsbar_mem hsbar_refl hrel' hdist' hncomm' hWb_closure rbar hrbarR hrbar_refl hrbarW
  have htbar_closure : tbar ∈ Subgroup.closure ((Wb : Set (↥H ≃ₗ[ZMod 3] ↥H)) ∪ {rbar}) := by
    rw [hfull]
    exact htbarR
  have hliftspec : ∀ b ∈ Subgroup.closure ((Wb : Set (↥H ≃ₗ[ZMod 3] ↥H)) ∪ {rbar}),
      ∃ m ∈ Subgroup.closure ((W : Set (V ≃ₗ[ZMod 3] V)) ∪ {r}), ggQ2s08k14_res H b m := by
    apply ggQ2s08k14_lift_bwd H ((Wb : Set (↥H ≃ₗ[ZMod 3] ↥H)) ∪ {rbar})
      ((W : Set (V ≃ₗ[ZMod 3] V)) ∪ {r})
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨w, hwW, hw_apply⟩ := hx
      exact ⟨w, Subgroup.subset_closure (Or.inl hwW), hw_apply⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨r, Subgroup.subset_closure (Or.inr (by simp)), hrbar_apply⟩
  obtain ⟨m, hm_mem, hm_res⟩ := hliftspec tbar htbar_closure
  have hmR : m ∈ R := by
    rw [hR]
    exact Subgroup.closure_mono (by
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Or.inr (by simp)) hm_mem
  set k : V ≃ₗ[ZMod 3] V := t * m⁻¹ with hkdef
  have hkH : ∀ h ∈ H, k h = h := by
    intro h hh
    rw [hkdef, LinearEquiv.mul_apply]
    have hmh : m⁻¹ h ∈ H := hRH m⁻¹ (R.inv_mem hmR) h hh
    have h1 : t (m⁻¹ h) = m (m⁻¹ h) := by
      simpa only [Subtype.coe_mk] using
        (htbar_apply ⟨m⁻¹ h, hmh⟩).symm.trans (hm_res ⟨m⁻¹ h, hmh⟩)
    rw [h1]
    simpa using LinearEquiv.apply_symm_apply m (h : V)
  have hkR : k ∈ R := by
    rw [hkdef]
    exact Subgroup.mul_mem _ htR (Subgroup.inv_mem _ hmR)
  obtain ⟨c, hc0, hcx⟩ :=
    ggQ2s08core_red_kernel_stab H xv hx hH R W hWR hRH hnt hWfix k hkR hkH
  have hkstab : k ∈ GGQ2S08LineStab R xv := ⟨hkR, c, hc0, hcx⟩
  have hkM0 : k ∈ GGQ2S08M0 R W r xv := Subgroup.subset_closure (Or.inr hkstab)
  have hmM0 : m ∈ GGQ2S08M0 R W r xv :=
    Subgroup.closure_mono (Set.subset_union_left) hm_mem
  have ht_eq : t = k * m := by
    rw [hkdef]
    group
  rw [ht_eq]
  exact Subgroup.mul_mem _ hkM0 hmM0

end CFSG.StandardType

end
