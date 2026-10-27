module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigIrr
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigRestrict

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private def ggQ2s08ch_res {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (b : ↥H ≃ₗ[ZMod 3] ↥H) (a : V ≃ₗ[ZMod 3] V) : Prop :=
  ∀ h : ↥H, ((b h : ↥H) : V) = a h

private lemma ggQ2s08ch_res_one {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) : ggQ2s08ch_res H 1 1 := by
  intro h
  rfl

private lemma ggQ2s08ch_res_mul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b b' : ↥H ≃ₗ[ZMod 3] ↥H} {a a' : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08ch_res H b a) (hb' : ggQ2s08ch_res H b' a') :
    ggQ2s08ch_res H (b * b') (a * a') := by
  intro h
  calc (((b * b') h : ↥H) : V) = a ((b' h : ↥H) : V) := hb (b' h)
    _ = a (a' h) := by rw [hb' h]
    _ = (a * a') h := rfl

private lemma ggQ2s08ch_res_inv {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b : ↥H ≃ₗ[ZMod 3] ↥H} {a : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08ch_res H b a) : ggQ2s08ch_res H b⁻¹ a⁻¹ := by
  intro h
  apply a.injective
  calc a (((b⁻¹) h : ↥H) : V) = ((b (b⁻¹ h) : ↥H) : V) := (hb (b⁻¹ h)).symm
    _ = (h : V) := by simp
    _ = a (a⁻¹ h) := by simp

private lemma ggQ2s08ch_res_unique {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b b' : ↥H ≃ₗ[ZMod 3] ↥H} {a : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08ch_res H b a) (hb' : ggQ2s08ch_res H b' a) : b = b' := by
  ext h
  rw [hb h, hb' h]

private lemma ggQ2s08ch_lift_closure_gen {A : Type} [Group A] {B : Type} [Group B]
    (rel : A → B → Prop) (hR1 : rel 1 1)
    (hRmul : ∀ {a a' : A} {b b' : B}, rel a b → rel a' b' → rel (a * a') (b * b'))
    (hRinv : ∀ {a : A} {b : B}, rel a b → rel a⁻¹ b⁻¹)
    (G : Set A) (Gbar : Set B)
    (hgen : ∀ x ∈ G, ∃ b ∈ Subgroup.closure Gbar, rel x b) :
    ∀ a ∈ Subgroup.closure G, ∃ b ∈ Subgroup.closure Gbar, rel a b := by
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

private lemma ggQ2s08ch_lift_fwd {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V)
    (G : Set (V ≃ₗ[ZMod 3] V)) (Gbar : Set (↥H ≃ₗ[ZMod 3] ↥H))
    (hgen : ∀ x ∈ G, ∃ b ∈ Subgroup.closure Gbar, ggQ2s08ch_res H b x) :
    ∀ a ∈ Subgroup.closure G, ∃ b ∈ Subgroup.closure Gbar, ggQ2s08ch_res H b a :=
  ggQ2s08ch_lift_closure_gen (A := V ≃ₗ[ZMod 3] V) (B := ↥H ≃ₗ[ZMod 3] ↥H)
    (fun a b => ggQ2s08ch_res H b a) (ggQ2s08ch_res_one H)
    (fun h1 h2 => ggQ2s08ch_res_mul H h1 h2)
    (fun h1 => ggQ2s08ch_res_inv H h1) G Gbar hgen

private lemma ggQ2s08ch_inv_le_line_absurd {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (xv : V)
    (hxmove : ¬ ∀ a ∈ R, ∀ u ∈ Submodule.span (ZMod 3) {xv},
      a u ∈ Submodule.span (ZMod 3) {xv})
    (S : Submodule (ZMod 3) V) (hS0 : S ≠ ⊥)
    (hSR : ∀ a ∈ R, ∀ u ∈ S, a u ∈ S)
    (hSle : S ≤ Submodule.span (ZMod 3) {xv}) : False := by
  obtain ⟨u, huS, hu0⟩ := (Submodule.ne_bot_iff S).mp hS0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hSle huS)
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hu0
    rw [← hc, hc0, zero_smul]
  have hxvS : xv ∈ S := by
    have hmem := S.smul_mem c⁻¹ huS
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at hmem
    exact hmem
  have hspanle : Submodule.span (ZMod 3) {xv} ≤ S :=
    (Submodule.span_singleton_le_iff_mem xv S).mpr hxvS
  have hSeq : S = Submodule.span (ZMod 3) {xv} := le_antisymm hSle hspanle
  apply hxmove
  intro a ha u hu
  rw [← hSeq]
  exact hSR a ha u (by rw [hSeq]; exact hu)

theorem ggQ2s08_bigC_hyper (hKG : GGReflClassLargeThree) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (hn : Module.finrank (ZMod 3) V = n) (h3 : 3 ∣ n) (h12 : 12 ≤ n)
    {W R : Subgroup (V ≃ₗ[ZMod 3] V)} {H : Submodule (ZMod 3) V} {xv : V}
    (hfinH : Module.finrank (ZMod 3) H = n - 2) (hxH : xv ∉ H)
    (hWH : ∀ w ∈ W, ∀ v, w v - v ∈ H) (hWcard : Nat.card W = n.factorial) (hWR : W ≤ R)
    (hWfaith : ∀ w ∈ W, (∀ u ∈ H, w u = u) → w = 1)
    (hdich : ∀ S : Submodule (ZMod 3) V, (∀ w ∈ W, ∀ u ∈ S, w u ∈ S) →
      S ≤ Submodule.span (ZMod 3) {xv} ∨ H ≤ S)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (hb : 8 * Nat.card R < 3 ^ ((n - 2) * (n - 3) / 2))
    (hxmove : ¬ ∀ a ∈ R, ∀ u ∈ Submodule.span (ZMod 3) {xv}, a u ∈ Submodule.span (ZMod 3) {xv})
    (hred : ¬ ∀ S : Submodule (ZMod 3) V, (∀ a ∈ R, ∀ u ∈ S, a u ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∀ g ∈ R, ∀ u ∈ H, g u ∈ H := by
  classical
  haveI : FiniteDimensional (ZMod 3) V := Module.finite_of_finrank_pos (by omega)
  haveI : Fintype V := Module.fintypeOfFintype (Module.Basis.ofVectorSpace (ZMod 3) V)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e1 e2 h => LinearEquiv.ext (fun v => congrFun h v))
  obtain ⟨S, hSnot⟩ := not_forall.mp hred
  rw [not_imp] at hSnot
  obtain ⟨hSR, hSnotor⟩ := hSnot
  rw [not_or] at hSnotor
  obtain ⟨hS0, hS1⟩ := hSnotor
  have hSW : ∀ w ∈ W, ∀ u ∈ S, w u ∈ S := fun w hw => hSR w (hWR hw)
  rcases hdich S hSW with hSle | hHle
  ·
    exact False.elim (ggQ2s08ch_inv_le_line_absurd R xv hxmove S hS0 hSR hSle)
  · by_cases hSH : S = H
    ·
      intro g hg u hu
      rw [← hSH] at hu ⊢
      exact hSR g hg u hu
    ·
      have hHltS : H < S := lt_of_le_of_ne hHle (Ne.symm hSH)
      have hSltTop : S < ⊤ := lt_of_le_of_ne le_top hS1
      haveI : FiniteDimensional (ZMod 3) ↥S :=
        FiniteDimensional.finiteDimensional_submodule S
      haveI : Finite (↥S ≃ₗ[ZMod 3] ↥S) :=
        Finite.of_injective (fun e : ↥S ≃ₗ[ZMod 3] ↥S => (e : ↥S → ↥S))
          (fun e1 e2 h => LinearEquiv.ext (fun v => congrFun h v))
      have h1 : Module.finrank (ZMod 3) H < Module.finrank (ZMod 3) S :=
        Submodule.finrank_lt_finrank_of_lt hHltS
      have h2 : Module.finrank (ZMod 3) S < Module.finrank (ZMod 3) V :=
        Submodule.finrank_lt hS1
      rw [hfinH] at h1
      rw [hn] at h2
      have hfinS : Module.finrank (ZMod 3) S = n - 1 := by omega
      have hWU : ∀ w ∈ W, ∀ u ∈ S, w u ∈ S := fun w hw => hSR w (hWR hw)
      let RU : Subgroup (↥S ≃ₗ[ZMod 3] ↥S) := GGQ2S08Res S R hSR
      let WU : Subgroup (↥S ≃ₗ[ZMod 3] ↥S) := GGQ2S08Res S W hWU
      have hWUR : WU ≤ RU := by
        intro b hb
        obtain ⟨a, haW, ha⟩ := hb
        exact ⟨a, hWR haW, ha⟩
      have hcardWU : Nat.card WU = n.factorial := by
        let f : ↥W → ↥WU := fun a =>
          ⟨Classical.choose (ggQ2s08core_res_mem S W hWU a.1 a.2),
            (Classical.choose_spec (ggQ2s08core_res_mem S W hWU a.1 a.2)).1⟩
        have hfspec : ∀ a : ↥W, ggQ2s08ch_res S (f a).1 a.1 := fun a =>
          (Classical.choose_spec (ggQ2s08core_res_mem S W hWU a.1 a.2)).2
        have hfinj : Function.Injective f := by
          intro a a' hff
          have hval : (f a).1 = (f a').1 := congrArg Subtype.val hff
          apply Subtype.ext
          have hfix : ∀ u ∈ H, ((a.1)⁻¹ * a'.1) u = u := by
            intro u hu
            have huS : u ∈ S := hHle hu
            have h2' := hfspec a' ⟨u, huS⟩
            have h1' := hfspec a ⟨u, huS⟩
            have hval_u : a'.1 u = a.1 u := by
              calc a'.1 u = (((f a').1 ⟨u, huS⟩ : ↥S) : V) := h2'.symm
                _ = (((f a).1 ⟨u, huS⟩ : ↥S) : V) := by rw [hval]
                _ = a.1 u := h1'
            rw [LinearEquiv.mul_apply, hval_u]
            exact LinearEquiv.symm_apply_apply (a.1) u
          have hw : (a.1)⁻¹ * a'.1 = 1 :=
            hWfaith ((a.1)⁻¹ * a'.1) (W.mul_mem (W.inv_mem a.2) a'.2) hfix
          exact inv_mul_eq_one.mp hw
        have hfsurj : Function.Surjective f := by
          intro b
          obtain ⟨a, haW, ha⟩ := b.2
          refine ⟨⟨a, haW⟩, ?_⟩
          apply Subtype.ext
          exact ggQ2s08ch_res_unique S (hfspec ⟨a, haW⟩) ha
        have hle1 : Nat.card ↥W ≤ Nat.card ↥WU := Nat.card_le_card_of_injective f hfinj
        have hle2 : Nat.card ↥WU ≤ Nat.card ↥W := Nat.card_le_card_of_surjective f hfsurj
        exact (le_antisymm hle2 hle1).trans hWcard
      have hcardRU : Nat.card RU ≤ Nat.card R := by
        let f : ↥R → ↥RU := fun a =>
          ⟨Classical.choose (ggQ2s08core_res_mem S R hSR a.1 a.2),
            (Classical.choose_spec (ggQ2s08core_res_mem S R hSR a.1 a.2)).1⟩
        have hfsurj : Function.Surjective f := by
          intro b
          obtain ⟨a, haR, ha⟩ := b.2
          refine ⟨⟨a, haR⟩, ?_⟩
          apply Subtype.ext
          exact ggQ2s08ch_res_unique S
            (Classical.choose_spec (ggQ2s08core_res_mem S R hSR a haR)).2 ha
        exact Nat.card_le_card_of_surjective f hfsurj
      have hgenU : RU = Subgroup.closure {r | r ∈ RU ∧ GGLinRefl r} := by
        apply le_antisymm
        · intro b hb
          obtain ⟨a, haR, ha⟩ := hb
          have hgenKU : ∀ x ∈ {r : V ≃ₗ[ZMod 3] V | r ∈ R ∧ GGLinRefl r},
              ∃ b' ∈ Subgroup.closure {r : ↥S ≃ₗ[ZMod 3] ↥S | r ∈ RU ∧ GGLinRefl r},
                ggQ2s08ch_res S b' x := by
            intro x hx
            obtain ⟨hxR, hxref⟩ := hx
            by_cases hfix : ∀ u : ↥S, x u = u
            · refine ⟨1, (Subgroup.closure _).one_mem, ?_⟩
              intro u
              simpa using (hfix u).symm
            · push Not at hfix
              obtain ⟨u, hu⟩ := hfix
              obtain ⟨b', hb'RU, hb'res, hb'refl⟩ :=
                ggQ2s08core_res_refl S R hSR x hxR hxref ⟨u, u.2, hu⟩
              exact ⟨b', Subgroup.subset_closure ⟨hb'RU, hb'refl⟩, hb'res⟩
          obtain ⟨b', hb'cl, hb'res⟩ :=
            ggQ2s08ch_lift_fwd S {r : V ≃ₗ[ZMod 3] V | r ∈ R ∧ GGLinRefl r}
              {r : ↥S ≃ₗ[ZMod 3] ↥S | r ∈ RU ∧ GGLinRefl r} hgenKU a
              (by rw [← hgen]; exact haR)
          have hbb' : b = b' := ggQ2s08ch_res_unique S ha hb'res
          simpa [hbb'] using hb'cl
        · rw [Subgroup.closure_le]
          rintro b ⟨hb, _⟩
          exact hb
      have hbU : 8 * Nat.card RU < 3 ^ ((n - 1) * ((n - 1) - 1) / 2) := by
        have hmul : 8 * Nat.card RU ≤ 8 * Nat.card R := Nat.mul_le_mul_left 8 hcardRU
        have hexp : (n - 2) * (n - 3) / 2 ≤ (n - 1) * ((n - 1) - 1) / 2 := by
          have he : (n - 1) * ((n - 1) - 1) = (n - 1) * (n - 2) := by
            rw [show (n - 1) - 1 = n - 2 by omega]
          rw [he]
          exact Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
        have hpow : 3 ^ ((n - 2) * (n - 3) / 2) ≤
            3 ^ ((n - 1) * ((n - 1) - 1) / 2) :=
          Nat.pow_le_pow_right (by norm_num) hexp
        exact lt_of_le_of_lt hmul (lt_of_lt_of_le hb hpow)
      have h3' : 3 ∣ (n - 1) + 1 := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
        exact h3
      have h11' : 11 ≤ n - 1 := by omega
      have hWcard' : Nat.card WU = ((n - 1) + 1).factorial := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
        exact hcardWU
      by_cases hirrU : ∀ T : Submodule (ZMod 3) ↥S,
          (∀ a ∈ RU, ∀ u ∈ T, a u ∈ T) → T = ⊥ ∨ T = ⊤
      ·
        exact False.elim (ggQ2s08_big_irr hKG hfinS h3' h11' hWcard' hWUR hgenU hbU hirrU)
      ·
        rw [not_forall] at hirrU
        obtain ⟨T, hTnot⟩ := hirrU
        rw [not_imp] at hTnot
        obtain ⟨hTU, hTnotor⟩ := hTnot
        rw [not_or] at hTnotor
        obtain ⟨hT0, hT1⟩ := hTnotor
        let S' : Submodule (ZMod 3) V := T.map S.subtype
        haveI : FiniteDimensional (ZMod 3) ↥S' :=
          FiniteDimensional.finiteDimensional_submodule S'
        have hS'leS : S' ≤ S := by
          rintro y ⟨t, _, rfl⟩
          exact t.2
        have hS'ne0 : S' ≠ ⊥ := by
          intro h
          apply hT0
          have hmap : T.map S.subtype = (⊥ : Submodule (ZMod 3) ↥S).map S.subtype := by
            rw [Submodule.map_bot]
            exact h
          exact Submodule.map_injective_of_injective S.injective_subtype hmap
        have hS'neS : S' ≠ S := by
          intro h
          apply hT1
          have hmap : T.map S.subtype = (⊤ : Submodule (ZMod 3) ↥S).map S.subtype := by
            rw [Submodule.map_top, Submodule.range_subtype]
            exact h
          exact Submodule.map_injective_of_injective S.injective_subtype hmap
        have hS'R : ∀ a ∈ R, ∀ u ∈ S', a u ∈ S' := by
          intro a ha u hu
          obtain ⟨t, htT, rfl⟩ := Submodule.mem_map.mp hu
          obtain ⟨b, hbRU, hbres⟩ := ggQ2s08core_res_mem S R hSR a ha
          exact Submodule.mem_map.mpr ⟨b t, hTU b hbRU t htT, hbres t⟩
        have hS'W : ∀ w ∈ W, ∀ u ∈ S', w u ∈ S' := fun w hw => hS'R w (hWR hw)
        rcases hdich S' hS'W with hS'span | hHS'
        · exact False.elim (ggQ2s08ch_inv_le_line_absurd R xv hxmove S' hS'ne0 hS'R hS'span)
        · have hlt : S' < S := lt_of_le_of_ne hS'leS hS'neS
          have h3fin : Module.finrank (ZMod 3) S' < Module.finrank (ZMod 3) S :=
            Submodule.finrank_lt_finrank_of_lt hlt
          have h4fin : Module.finrank (ZMod 3) H ≤ Module.finrank (ZMod 3) S' :=
            Submodule.finrank_mono hHS'
          rw [hfinS] at h3fin
          rw [hfinH] at h4fin
          have hfinS' : Module.finrank (ZMod 3) S' = n - 2 := by omega
          have hHS'eq : H = S' :=
            Submodule.eq_of_le_of_finrank_eq hHS' (by rw [hfinH, hfinS'])
          intro g hg u hu
          rw [hHS'eq] at hu ⊢
          exact hS'R g hg u hu

end CFSG.StandardType

end
