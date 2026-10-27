module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigIrr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private def ggQ2s08ar_res {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (b : ↥H ≃ₗ[ZMod 3] ↥H) (a : V ≃ₗ[ZMod 3] V) : Prop :=
  ∀ h : ↥H, ((b h : ↥H) : V) = a h

private lemma ggQ2s08ar_res_one {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) : ggQ2s08ar_res H 1 1 := by
  intro h
  rfl

private lemma ggQ2s08ar_res_mul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b b' : ↥H ≃ₗ[ZMod 3] ↥H} {a a' : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08ar_res H b a) (hb' : ggQ2s08ar_res H b' a') :
    ggQ2s08ar_res H (b * b') (a * a') := by
  intro h
  calc (((b * b') h : ↥H) : V) = a ((b' h : ↥H) : V) := hb (b' h)
    _ = a (a' h) := by rw [hb' h]
    _ = (a * a') h := rfl

private lemma ggQ2s08ar_res_inv {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b : ↥H ≃ₗ[ZMod 3] ↥H} {a : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08ar_res H b a) : ggQ2s08ar_res H b⁻¹ a⁻¹ := by
  intro h
  apply a.injective
  calc a (((b⁻¹) h : ↥H) : V) = ((b (b⁻¹ h) : ↥H) : V) := (hb (b⁻¹ h)).symm
    _ = (h : V) := by simp
    _ = a (a⁻¹ h) := by simp

private lemma ggQ2s08ar_res_unique {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b b' : ↥H ≃ₗ[ZMod 3] ↥H} {a : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08ar_res H b a) (hb' : ggQ2s08ar_res H b' a) : b = b' := by
  ext h
  rw [hb h, hb' h]

private lemma ggQ2s08ar_lift_closure_gen {A : Type} [Group A] {B : Type} [Group B]
    (Rel : A → B → Prop) (hRel1 : Rel 1 1)
    (hRelmul : ∀ {a a' : A} {b b' : B}, Rel a b → Rel a' b' → Rel (a * a') (b * b'))
    (hRelinv : ∀ {a : A} {b : B}, Rel a b → Rel a⁻¹ b⁻¹)
    (G : Set A) (Gbar : Set B)
    (hgen : ∀ x ∈ G, ∃ b ∈ Subgroup.closure Gbar, Rel x b) :
    ∀ a ∈ Subgroup.closure G, ∃ b ∈ Subgroup.closure Gbar, Rel a b := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one => exact ⟨1, (Subgroup.closure Gbar).one_mem, hRel1⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨bx, hbx, hbxr⟩ := ihx
      obtain ⟨byy, hby, hbyr⟩ := ihy
      exact ⟨bx * byy, (Subgroup.closure Gbar).mul_mem hbx hby, hRelmul hbxr hbyr⟩
  | inv x _ ihx =>
      obtain ⟨bx, hbx, hbxr⟩ := ihx
      exact ⟨bx⁻¹, (Subgroup.closure Gbar).inv_mem hbx, hRelinv hbxr⟩

private lemma ggQ2s08ar_lift_fwd {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V)
    (G : Set (V ≃ₗ[ZMod 3] V)) (Gbar : Set (↥H ≃ₗ[ZMod 3] ↥H))
    (hgen : ∀ x ∈ G, ∃ b ∈ Subgroup.closure Gbar, ggQ2s08ar_res H b x) :
    ∀ a ∈ Subgroup.closure G, ∃ b ∈ Subgroup.closure Gbar, ggQ2s08ar_res H b a :=
  ggQ2s08ar_lift_closure_gen (A := V ≃ₗ[ZMod 3] V) (B := ↥H ≃ₗ[ZMod 3] ↥H)
    (fun a b => ggQ2s08ar_res H b a) (ggQ2s08ar_res_one H)
    (fun h1 h2 => ggQ2s08ar_res_mul H h1 h2)
    (fun h1 => ggQ2s08ar_res_inv H h1) G Gbar hgen

private lemma ggQ2s08ar_inv_le_line_absurd {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
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

theorem ggQ2s08_bigA_red (hKG : GGReflClassLargeThree) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (hn : Module.finrank (ZMod 3) V = n) (h3 : 3 ∣ n) (h12 : 12 ≤ n)
    {W R : Subgroup (V ≃ₗ[ZMod 3] V)} {U : Submodule (ZMod 3) V} {xv : V}
    (hfinU : Module.finrank (ZMod 3) U = n - 1) (hxU : xv ∈ U)
    (hWU : ∀ w ∈ W, ∀ v, w v - v ∈ U) (hWcard : Nat.card W = n.factorial) (hWR : W ≤ R)
    (hWfaith : ∀ w ∈ W, (∀ u ∈ U, w u = u) → w = 1)
    (hdich : ∀ S : Submodule (ZMod 3) V, (∀ w ∈ W, ∀ u ∈ S, w u ∈ S) →
      S ≤ Submodule.span (ZMod 3) {xv} ∨ U ≤ S)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (hb : 8 * Nat.card R < 3 ^ ((n - 1) * (n - 2) / 2))
    (hxmove : ¬ ∀ a ∈ R, ∀ u ∈ Submodule.span (ZMod 3) {xv}, a u ∈ Submodule.span (ZMod 3) {xv})
    (hred : ¬ ∀ S : Submodule (ZMod 3) V, (∀ a ∈ R, ∀ u ∈ S, a u ∈ S) → S = ⊥ ∨ S = ⊤) :
    False := by
  classical
  haveI : FiniteDimensional (ZMod 3) V := Module.finite_of_finrank_pos (by omega)
  haveI : Fintype V := Module.fintypeOfFintype (Module.Basis.ofVectorSpace (ZMod 3) V)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e1 e2 h => LinearEquiv.ext (fun v => congrFun h v))
  haveI : Finite (↥U ≃ₗ[ZMod 3] ↥U) :=
    Finite.of_injective (fun e : ↥U ≃ₗ[ZMod 3] ↥U => (e : ↥U → ↥U))
      (fun e1 e2 h => LinearEquiv.ext (fun v => congrFun h v))
  obtain ⟨S, hSnot⟩ := not_forall.mp hred
  rw [not_imp] at hSnot
  obtain ⟨hSR, hSnotor⟩ := hSnot
  rw [not_or] at hSnotor
  obtain ⟨hS0, hS1⟩ := hSnotor
  have hSW : ∀ w ∈ W, ∀ u ∈ S, w u ∈ S := fun w hw => hSR w (hWR hw)
  rcases hdich S hSW with hSle | hUle
  ·
    exact False.elim (ggQ2s08ar_inv_le_line_absurd R xv hxmove S hS0 hSR hSle)
  ·
    have h1 : Module.finrank (ZMod 3) U ≤ Module.finrank (ZMod 3) S :=
      Submodule.finrank_mono hUle
    have h2 : Module.finrank (ZMod 3) S < Module.finrank (ZMod 3) V :=
      Submodule.finrank_lt hS1
    rw [hfinU] at h1
    rw [hn] at h2
    have hfinS : Module.finrank (ZMod 3) S = n - 1 := by omega
    have hUS : U = S := Submodule.eq_of_le_of_finrank_eq hUle (by rw [hfinU, hfinS])
    have hUR : ∀ a ∈ R, ∀ u ∈ U, a u ∈ U := by
      intro a ha u hu
      rw [hUS] at hu ⊢
      exact hSR a ha u hu
    have hUW : ∀ w ∈ W, ∀ u ∈ U, w u ∈ U := fun w hw => hUR w (hWR hw)
    let RU : Subgroup (↥U ≃ₗ[ZMod 3] ↥U) := GGQ2S08Res U R hUR
    let WU : Subgroup (↥U ≃ₗ[ZMod 3] ↥U) := GGQ2S08Res U W hUW
    have hWUR : WU ≤ RU := by
      intro b hb
      obtain ⟨a, haW, ha⟩ := hb
      exact ⟨a, hWR haW, ha⟩
    have hcardWU : Nat.card WU = n.factorial := by
      let f : ↥W → ↥WU := fun a =>
        ⟨Classical.choose (ggQ2s08core_res_mem U W hUW a.1 a.2),
          (Classical.choose_spec (ggQ2s08core_res_mem U W hUW a.1 a.2)).1⟩
      have hfspec : ∀ a : ↥W, ggQ2s08ar_res U (f a).1 a.1 := fun a =>
        (Classical.choose_spec (ggQ2s08core_res_mem U W hUW a.1 a.2)).2
      have hfinj : Function.Injective f := by
        intro a a' hff
        have hval : (f a).1 = (f a').1 := congrArg Subtype.val hff
        apply Subtype.ext
        have hfix : ∀ u ∈ U, ((a.1)⁻¹ * a'.1) u = u := by
          intro u hu
          have heq : a.1 u = a'.1 u := by
            have h1 : ((f a).1 ⟨u, hu⟩ : V) = a.1 u := hfspec a ⟨u, hu⟩
            have h2 : ((f a').1 ⟨u, hu⟩ : V) = a'.1 u := hfspec a' ⟨u, hu⟩
            rw [← h1, hval, h2]
          rw [LinearEquiv.mul_apply, heq.symm]
          exact LinearEquiv.symm_apply_apply (a.1) u
        have hw : (a.1)⁻¹ * a'.1 = 1 :=
          hWfaith _ (W.mul_mem (W.inv_mem a.2) a'.2) hfix
        exact inv_mul_eq_one.mp hw
      have hfsurj : Function.Surjective f := by
        intro b
        obtain ⟨a, haW, ha⟩ := b.2
        refine ⟨⟨a, haW⟩, ?_⟩
        apply Subtype.ext
        exact ggQ2s08ar_res_unique U (hfspec ⟨a, haW⟩) ha
      have hle1 : Nat.card ↥W ≤ Nat.card ↥WU := Nat.card_le_card_of_injective f hfinj
      have hle2 : Nat.card ↥WU ≤ Nat.card ↥W := Nat.card_le_card_of_surjective f hfsurj
      exact (le_antisymm hle2 hle1).trans hWcard
    have hcardRU : Nat.card RU ≤ Nat.card R := by
      let f : ↥R → ↥RU := fun a =>
        ⟨Classical.choose (ggQ2s08core_res_mem U R hUR a.1 a.2),
          (Classical.choose_spec (ggQ2s08core_res_mem U R hUR a.1 a.2)).1⟩
      have hfsurj : Function.Surjective f := by
        intro b
        obtain ⟨a, haR, ha⟩ := b.2
        refine ⟨⟨a, haR⟩, ?_⟩
        apply Subtype.ext
        exact ggQ2s08ar_res_unique U
          (Classical.choose_spec (ggQ2s08core_res_mem U R hUR a haR)).2 ha
      exact Nat.card_le_card_of_surjective f hfsurj
    have hgenU : RU = Subgroup.closure {r | r ∈ RU ∧ GGLinRefl r} := by
      apply le_antisymm
      · intro b hb
        obtain ⟨a, haR, ha⟩ := hb
        have hgenKU : ∀ x ∈ {r : V ≃ₗ[ZMod 3] V | r ∈ R ∧ GGLinRefl r},
            ∃ b' ∈ Subgroup.closure {r : ↥U ≃ₗ[ZMod 3] ↥U | r ∈ RU ∧ GGLinRefl r},
              ggQ2s08ar_res U b' x := by
          intro x hx
          obtain ⟨hxR, hxref⟩ := hx
          by_cases hfix : ∀ u : ↥U, x u = u
          · refine ⟨1, (Subgroup.closure _).one_mem, ?_⟩
            intro u
            simpa using (hfix u).symm
          · push Not at hfix
            obtain ⟨u, hu⟩ := hfix
            obtain ⟨b', hb'RU, hb'res, hb'refl⟩ :=
              ggQ2s08core_res_refl U R hUR x hxR hxref ⟨u, u.2, hu⟩
            exact ⟨b', Subgroup.subset_closure ⟨hb'RU, hb'refl⟩, hb'res⟩
        obtain ⟨b', hb'cl, hb'res⟩ :=
          ggQ2s08ar_lift_fwd U {r : V ≃ₗ[ZMod 3] V | r ∈ R ∧ GGLinRefl r}
            {r : ↥U ≃ₗ[ZMod 3] ↥U | r ∈ RU ∧ GGLinRefl r} hgenKU a
            (by rw [← hgen]; exact haR)
        have hbb' : b = b' := ggQ2s08ar_res_unique U ha hb'res
        simpa [hbb'] using hb'cl
      · rw [Subgroup.closure_le]
        rintro b ⟨hb, _⟩
        exact hb
    have hbU : 8 * Nat.card RU < 3 ^ ((n - 1) * ((n - 1) - 1) / 2) := by
      have hmul : 8 * Nat.card RU ≤ 8 * Nat.card R := Nat.mul_le_mul_left 8 hcardRU
      have he : (n - 1) * ((n - 1) - 1) = (n - 1) * (n - 2) := by
        rw [show (n - 1) - 1 = n - 2 by omega]
      rw [he]
      exact lt_of_le_of_lt hmul hb
    have hirrU : ∀ T : Submodule (ZMod 3) ↥U,
        (∀ a ∈ RU, ∀ u ∈ T, a u ∈ T) → T = ⊥ ∨ T = ⊤ := by
      intro T hT
      by_cases hT0 : T = ⊥
      · exact Or.inl hT0
      · right
        let S' : Submodule (ZMod 3) V := T.map U.subtype
        have hS'leU : S' ≤ U := by
          rintro y ⟨t, _, rfl⟩
          exact t.2
        have hS'ne0 : S' ≠ ⊥ := by
          intro h
          apply hT0
          have hmap : T.map U.subtype = (⊥ : Submodule (ZMod 3) ↥U).map U.subtype := by
            rw [Submodule.map_bot]
            exact h
          exact Submodule.map_injective_of_injective U.injective_subtype hmap
        have hS'R : ∀ a ∈ R, ∀ u ∈ S', a u ∈ S' := by
          intro a ha u hu
          obtain ⟨t, htT, rfl⟩ := Submodule.mem_map.mp hu
          obtain ⟨b, hbRU, hbres⟩ := ggQ2s08core_res_mem U R hUR a ha
          exact Submodule.mem_map.mpr ⟨b t, hT b hbRU t htT, hbres t⟩
        have hS'W : ∀ w ∈ W, ∀ u ∈ S', w u ∈ S' := fun w hw => hS'R w (hWR hw)
        rcases hdich S' hS'W with hspan | hUS'
        · exact False.elim (ggQ2s08ar_inv_le_line_absurd R xv hxmove S' hS'ne0 hS'R hspan)
        · have hS'eq : S' = U := le_antisymm hS'leU hUS'
          have hmap : T.map U.subtype = (⊤ : Submodule (ZMod 3) ↥U).map U.subtype := by
            rw [Submodule.map_top, Submodule.range_subtype]
            exact hS'eq
          exact Submodule.map_injective_of_injective U.injective_subtype hmap
    have h3' : 3 ∣ (n - 1) + 1 := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact h3
    have h11' : 11 ≤ n - 1 := by omega
    have hWcard' : Nat.card WU = ((n - 1) + 1).factorial := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact hcardWU
    exact ggQ2s08_big_irr hKG hfinU h3' h11' hWcard' hWUR hgenU hbU hirrU

end CFSG.StandardType

end
