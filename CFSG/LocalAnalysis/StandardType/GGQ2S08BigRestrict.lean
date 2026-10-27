module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreRes
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreAbs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreClassify
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSPerm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

private def ggQ2s08tbr_res {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) (b : ↥H ≃ₗ[ZMod 3] ↥H) (a : V ≃ₗ[ZMod 3] V) : Prop :=
  ∀ h : ↥H, ((b h : ↥H) : V) = a h

private lemma ggQ2s08tbr_res_one {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) : ggQ2s08tbr_res H 1 1 := by
  intro h
  rfl

private lemma ggQ2s08tbr_res_mul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b b' : ↥H ≃ₗ[ZMod 3] ↥H} {a a' : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08tbr_res H b a) (hb' : ggQ2s08tbr_res H b' a') :
    ggQ2s08tbr_res H (b * b') (a * a') := by
  intro h
  calc (((b * b') h : ↥H) : V) = a ((b' h : ↥H) : V) := hb (b' h)
    _ = a (a' h) := by rw [hb' h]
    _ = (a * a') h := rfl

private lemma ggQ2s08tbr_res_inv {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b : ↥H ≃ₗ[ZMod 3] ↥H} {a : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08tbr_res H b a) : ggQ2s08tbr_res H b⁻¹ a⁻¹ := by
  intro h
  apply a.injective
  calc a (((b⁻¹) h : ↥H) : V) = ((b (b⁻¹ h) : ↥H) : V) := (hb (b⁻¹ h)).symm
    _ = (h : V) := by simp
    _ = a (a⁻¹ h) := by simp

private lemma ggQ2s08tbr_res_unique {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V) {b b' : ↥H ≃ₗ[ZMod 3] ↥H} {a : V ≃ₗ[ZMod 3] V}
    (hb : ggQ2s08tbr_res H b a) (hb' : ggQ2s08tbr_res H b' a) : b = b' := by
  ext h
  rw [hb h, hb' h]

private lemma ggQ2s08tbr_lift_closure_gen {A : Type} [Group A] {B : Type} [Group B]
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

private lemma ggQ2s08tbr_lift_fwd {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (H : Submodule (ZMod 3) V)
    (G : Set (V ≃ₗ[ZMod 3] V)) (Gbar : Set (↥H ≃ₗ[ZMod 3] ↥H))
    (hgen : ∀ x ∈ G, ∃ b ∈ Subgroup.closure Gbar, ggQ2s08tbr_res H b x) :
    ∀ a ∈ Subgroup.closure G, ∃ b ∈ Subgroup.closure Gbar, ggQ2s08tbr_res H b a :=
  ggQ2s08tbr_lift_closure_gen (A := V ≃ₗ[ZMod 3] V) (B := ↥H ≃ₗ[ZMod 3] ↥H)
    (fun a b => ggQ2s08tbr_res H b a) (ggQ2s08tbr_res_one H)
    (fun h1 h2 => ggQ2s08tbr_res_mul H h1 h2)
    (fun h1 => ggQ2s08tbr_res_inv H h1) G Gbar hgen

theorem ggQ2s08_big_restrict (hKG : GGReflClassLargeThree) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Module.Finite (ZMod 3) V] {d : ℕ} (h3 : 3 ∣ d + 2) (h10 : 10 ≤ d)
    {W R : Subgroup (V ≃ₗ[ZMod 3] V)} {H : Submodule (ZMod 3) V}
    (hfinH : Module.finrank (ZMod 3) H = d) (hWcard : Nat.card W = (d + 2).factorial)
    (hWR : W ≤ R) (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (hpres : ∀ g ∈ R, ∀ u ∈ H, g u ∈ H)
    (hWirr : ∀ S : Submodule (ZMod 3) V, S ≤ H → (∀ w ∈ W, ∀ u ∈ S, w u ∈ S) → S = ⊥ ∨ S = H)
    (hWfaith : ∀ w ∈ W, (∀ u ∈ H, w u = u) → w = 1)
    (hb : 8 * Nat.card R < 3 ^ (d * (d - 1) / 2)) :
    ∀ g ∈ R, ∃ w ∈ W, ∀ u ∈ H, g u = w u := by
  classical
  haveI : Fintype V := Module.fintypeOfFintype (Module.Basis.ofVectorSpace (ZMod 3) V)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e1 e2 h => LinearEquiv.ext (fun v => congrFun h v))
  haveI : Module.Finite (ZMod 3) ↥H := Module.finite_of_finrank_pos (by rw [hfinH]; omega)
  haveI : Fintype ↥H := Module.fintypeOfFintype (Module.Basis.ofVectorSpace (ZMod 3) ↥H)
  haveI : Finite (↥H ≃ₗ[ZMod 3] ↥H) :=
    Finite.of_injective (fun e : ↥H ≃ₗ[ZMod 3] ↥H => (e : ↥H → ↥H))
      (fun e1 e2 h => LinearEquiv.ext (fun v => congrFun h v))
  let Rb : Subgroup (↥H ≃ₗ[ZMod 3] ↥H) := GGQ2S08Res H R hpres
  have hWH : ∀ a ∈ W, ∀ h ∈ H, a h ∈ H := fun a ha => hpres a (hWR ha)
  let Wb : Subgroup (↥H ≃ₗ[ZMod 3] ↥H) := GGQ2S08Res H W hWH
  have hWbR : Wb ≤ Rb := by
    rintro b ⟨a, haW, ha⟩
    exact ⟨a, hWR haW, ha⟩
  have hcardWb : Nat.card Wb = Nat.card W := by
    let f : ↥W → ↥Wb := fun a =>
      ⟨Classical.choose (ggQ2s08core_res_mem H W hWH a.1 a.2),
        (Classical.choose_spec (ggQ2s08core_res_mem H W hWH a.1 a.2)).1⟩
    have hinj : Function.Injective f := by
      intro a1 a2 h
      apply Subtype.ext
      have hval : (f a1).1 = (f a2).1 := congrArg Subtype.val h
      have hchoose1 := (Classical.choose_spec (ggQ2s08core_res_mem H W hWH a1.1 a1.2)).2
      have hchoose2 := (Classical.choose_spec (ggQ2s08core_res_mem H W hWH a2.1 a2.2)).2
      have hfix : ∀ u ∈ H, (a1.1⁻¹ * a2.1) u = u := by
        intro u hu
        have heq : a1.1 u = a2.1 u := by
          have h1 : ((f a1).1 ⟨u, hu⟩ : V) = a1.1 u := hchoose1 ⟨u, hu⟩
          have h2 : ((f a2).1 ⟨u, hu⟩ : V) = a2.1 u := hchoose2 ⟨u, hu⟩
          rw [← h1, hval, h2]
        rw [LinearEquiv.mul_apply, heq.symm]
        simp
      have hk1 : a1.1⁻¹ * a2.1 = 1 :=
        hWfaith _ (W.mul_mem (W.inv_mem a1.2) a2.2) hfix
      have h2 : a2.1 = a1.1 := by
        have := congrArg (fun e : V ≃ₗ[ZMod 3] V => a1.1 * e) hk1
        simpa [mul_assoc] using this
      exact h2.symm
    have hsurj : Function.Surjective f := by
      intro b
      obtain ⟨a, haW, ha⟩ := b.2
      refine ⟨⟨a, haW⟩, ?_⟩
      apply Subtype.ext
      exact ggQ2s08tbr_res_unique H
        (Classical.choose_spec (ggQ2s08core_res_mem H W hWH a haW)).2 ha
    exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
  have hWb_card_fact : Nat.card Wb = (d + 2).factorial := by
    rw [hcardWb, hWcard]
  have hfac_eq : (d + 2).factorial = (d + 2) * (d + 1).factorial := by
    rw [show d + 2 = (d + 1) + 1 by omega, Nat.factorial_succ]
  have hfac_lt : (d + 1).factorial < (d + 2).factorial := by
    rw [hfac_eq]
    calc (d + 1).factorial = 1 * (d + 1).factorial := (one_mul _).symm
      _ < (d + 2) * (d + 1).factorial :=
          Nat.mul_lt_mul_of_pos_right (by omega : 1 < d + 2) (Nat.factorial_pos (d + 1))
  have hfac_gt_one : 1 < (d + 2).factorial := by
    have hpos := Nat.factorial_pos (d + 1)
    omega
  have hirr : ∀ S : Submodule (ZMod 3) ↥H,
      (∀ a ∈ Rb, ∀ u ∈ S, a u ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hTle : S.map H.subtype ≤ H := by
      rintro y ⟨x, hx, rfl⟩
      exact x.2
    have hWinv : ∀ w ∈ W, ∀ u ∈ S.map H.subtype, w u ∈ S.map H.subtype := by
      intro w hw u hu
      obtain ⟨x, hxS, rfl⟩ := hu
      obtain ⟨b, hbR, hbapply⟩ := ggQ2s08core_res_mem H R hpres w (hWR hw)
      have hmem : b x ∈ S := hS b hbR x hxS
      exact ⟨b x, hmem, hbapply x⟩
    rcases hWirr (S.map H.subtype) hTle hWinv with h | h
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
  have hgen' : Rb = Subgroup.closure
      {a : ↥H ≃ₗ[ZMod 3] ↥H | a ∈ Rb ∧ GGLinRefl a} := by
    apply le_antisymm
    · intro b hb
      obtain ⟨g, hgR, hbres⟩ := hb
      have hgG : g ∈ Subgroup.closure {r : V ≃ₗ[ZMod 3] V | r ∈ R ∧ GGLinRefl r} := by
        rw [← hgen]
        exact hgR
      have hgen_fwd : ∀ x ∈ {r : V ≃ₗ[ZMod 3] V | r ∈ R ∧ GGLinRefl r},
          ∃ b ∈ Subgroup.closure {a : ↥H ≃ₗ[ZMod 3] ↥H | a ∈ Rb ∧ GGLinRefl a},
            ggQ2s08tbr_res H b x := by
        intro x hx
        obtain ⟨hxR, hxrefl⟩ := hx
        by_cases hne : ∃ h ∈ H, x h ≠ h
        · obtain ⟨bb, hbbR, hbbapply, hbbrefl⟩ :=
            ggQ2s08core_res_refl H R hpres x hxR hxrefl hne
          exact ⟨bb, Subgroup.subset_closure ⟨hbbR, hbbrefl⟩, hbbapply⟩
        · push Not at hne
          refine ⟨1, Subgroup.one_mem _, ?_⟩
          intro h
          change ((h : ↥H) : V) = x (h : V)
          exact (hne (h : V) h.2).symm
      obtain ⟨b', hb', hb'res⟩ :=
        ggQ2s08tbr_lift_fwd H {r : V ≃ₗ[ZMod 3] V | r ∈ R ∧ GGLinRefl r}
          {a : ↥H ≃ₗ[ZMod 3] ↥H | a ∈ Rb ∧ GGLinRefl a} hgen_fwd g hgG
      have hbb' : b = b' := ggQ2s08tbr_res_unique H hbres hb'res
      rw [hbb']
      exact hb'
    · rw [Subgroup.closure_le]
      rintro a ⟨ha, _⟩
      exact ha
  have hWb_ne_bot : Wb ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card Wb = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hWb_card_fact] at hcard1
    omega
  have hRb_ne_bot : Rb ≠ ⊥ := by
    intro hbot
    exact hWb_ne_bot (le_bot_iff.mp (hbot ▸ hWbR))
  have hex : ∃ r ∈ Rb, GGLinRefl r := by
    by_contra hcon
    push Not at hcon
    have hempty : {a : ↥H ≃ₗ[ZMod 3] ↥H | a ∈ Rb ∧ GGLinRefl a} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨ha, hr⟩
      exact hcon a ha hr
    exact hRb_ne_bot (by rw [hgen', hempty, Subgroup.closure_empty])
  have habs : ZS.AbsIrred 3 Rb :=
    ggQ2s08core_absIrred_of_irred Rb hgen' hex hirr
  have hcard_Rb : Nat.card Rb ≤ Nat.card R := by
    let f : ↥R → ↥Rb := fun a =>
      ⟨Classical.choose (ggQ2s08core_res_mem H R hpres a.1 a.2),
        (Classical.choose_spec (ggQ2s08core_res_mem H R hpres a.1 a.2)).1⟩
    have hf : Function.Surjective f := by
      intro b
      obtain ⟨a, haR, ha⟩ := b.2
      refine ⟨⟨a, haR⟩, ?_⟩
      apply Subtype.ext
      exact ggQ2s08tbr_res_unique H
        (Classical.choose_spec (ggQ2s08core_res_mem H R hpres a haR)).2 ha
    exact Nat.card_le_card_of_surjective f hf
  have hsmall_Rb : 8 * Nat.card Rb < 3 ^ (d * (d - 1) / 2) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 8 hcard_Rb) hb
  have hpm1 : ∀ c : ZMod 3, c ≠ 0 ↔ (c = 1 ∨ c = -1) := by decide
  have hdiv2 : (d + 2).factorial ∣ Nat.card Rb := by
    rw [← hWb_card_fact]
    exact Subgroup.card_dvd_of_le hWbR
  have hmono_false : ∀ (b : Module.Basis (Fin d) (ZMod 3) ↥H),
      Rb ≤ OrthF3.ggOrthSignedPerms b → False := by
    intro b hle
    have hdiv1 : Nat.card Rb ∣ 2 ^ d * d.factorial := by
      calc Nat.card Rb ∣ Nat.card ↥(OrthF3.ggOrthSignedPerms b) :=
            Subgroup.card_dvd_of_le hle
        _ = 2 ^ d * d.factorial := OrthF3.card_ggOrthSignedPerms b
    have hdvd : (d + 2).factorial ∣ 2 ^ d * d.factorial := dvd_trans hdiv2 hdiv1
    have h1 : (d + 2).factorial = (d + 2) * (d + 1) * d.factorial := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; ring
    rw [h1] at hdvd
    have h2 : (d + 2) * (d + 1) ∣ 2 ^ d :=
      Nat.dvd_of_mul_dvd_mul_right (Nat.factorial_pos d) hdvd
    have h3' : 3 ∣ (d + 2) * (d + 1) := dvd_mul_of_dvd_left h3 (d + 1)
    have h3pow : 3 ∣ 2 ^ d := h3'.trans h2
    have h32 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3pow
    norm_num at h32
  have hperm1_false : ∀ e : Rb ≃* Equiv.Perm (Fin (d + 1)), False := by
    intro e
    have hcard : Nat.card Rb = (d + 1).factorial := by
      calc Nat.card Rb = Nat.card (Equiv.Perm (Fin (d + 1))) := Nat.card_congr e.toEquiv
        _ = (d + 1).factorial := by rw [Nat.card_perm]; simp [Nat.card_eq_fintype_card]
    have hRb_pos : 0 < Nat.card Rb := by
      have hle1 : Nat.card Wb ≤ Nat.card Rb := Subgroup.card_le_of_le hWbR
      rw [hWb_card_fact] at hle1
      exact lt_of_lt_of_le (Nat.factorial_pos (d + 2)) hle1
    have hle : (d + 2).factorial ≤ Nat.card Rb := Nat.le_of_dvd hRb_pos hdiv2
    rw [hcard] at hle
    exact absurd hle (not_le_of_gt hfac_lt)
  have hgoal : Rb = Wb := by
    rcases ggRC_classify_frame3 hKG hfinH (by omega) Rb habs hgen' hsmall_Rb with
      ⟨b, hmono | hmonoE⟩ | ⟨e, _⟩ | ⟨e, _⟩
    · exact (hmono_false b (by
        intro a ha
        obtain ⟨σ, ε, hεne, hap⟩ := (hmono a).mp ha
        exact ⟨σ, ε, fun i => (hpm1 (ε i)).1 (hεne i), hap⟩)).elim
    · exact (hmono_false b (by
        intro a ha
        obtain ⟨σ, ε, hεne, _, hap⟩ := (hmonoE a).mp ha
        exact ⟨σ, ε, fun i => (hpm1 (ε i)).1 (hεne i), hap⟩)).elim
    · exact (hperm1_false e).elim
    · have hcard : Nat.card Rb = (d + 2).factorial := by
        calc Nat.card Rb = Nat.card (Equiv.Perm (Fin (d + 2))) := Nat.card_congr e.toEquiv
          _ = (d + 2).factorial := by rw [Nat.card_perm]; simp [Nat.card_eq_fintype_card]
      have hcardle : Nat.card Rb ≤ Nat.card Wb := by rw [hcard, hWb_card_fact]
      exact (Subgroup.eq_of_le_of_card_ge hWbR hcardle).symm
  intro g hg
  obtain ⟨b, hbRb, hbapply⟩ := ggQ2s08core_res_mem H R hpres g hg
  have hbWb : b ∈ Wb := hgoal ▸ hbRb
  obtain ⟨w, hwW, hwapply⟩ := hbWb
  refine ⟨w, hwW, fun u hu => ?_⟩
  exact (hbapply ⟨u, hu⟩).symm.trans (hwapply ⟨u, hu⟩)

end CFSG.StandardType

end
