module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN5
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN6
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN8t
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Rep3
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKLin

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Quasithin.H13.L829N
open Module Matrix

private theorem nk_isSimple {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {Sg : Subgroup (W ≃ₗ[ZMod 2] W)} {P : Submodule (ZMod 2) W}
    (hPne : P ≠ ⊥) (hPinv : InvUnder Sg P)
    (hmin : ∀ Q : Submodule (ZMod 2) W, Q ≤ P → InvUnder Sg Q → Q = ⊥ ∨ Q = P) :
    IsSimpleModule (algOf Sg) ↥(toSubmoduleA Sg P hPinv) := by
  have hXne : toSubmoduleA Sg P hPinv ≠ ⊥ := by
    intro hX
    apply hPne
    rw [Submodule.eq_bot_iff] at hX ⊢
    exact fun x hx => hX x hx
  have hatom : ∀ b : Submodule (algOf Sg) W, b ≤ toSubmoduleA Sg P hPinv →
      b = ⊥ ∨ b = toSubmoduleA Sg P hPinv := by
    intro b hb
    have hbF : toSubmoduleF2 Sg b ≤ P := fun w hw => hb hw
    rcases hmin (toSubmoduleF2 Sg b) hbF (invUnder_of_submoduleA Sg b) with h0 | h0
    · left
      ext w
      constructor
      · intro hw
        have hw' : w ∈ toSubmoduleF2 Sg b := hw
        rw [h0, Submodule.mem_bot] at hw'
        rw [Submodule.mem_bot, hw']
      · intro hw
        rw [Submodule.mem_bot] at hw
        rw [hw]
        exact b.zero_mem
    · right
      ext w
      constructor
      · exact fun hw => hb hw
      · intro hw
        have hw' : w ∈ toSubmoduleF2 Sg b := by
          rw [h0]
          exact hw
        exact hw'
  refine isSimpleModule_iff_isAtom.mpr ?_
  show toSubmoduleA Sg P hPinv ≠ ⊥ ∧ ∀ b : Submodule (algOf Sg) W,
    b < toSubmoduleA Sg P hPinv → b = ⊥
  exact ⟨hXne, fun b hb => (hatom b hb.le).resolve_right hb.ne⟩

private theorem nk_rep_aux {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {Sg Gg Tg Vg : Subgroup (W ≃ₗ[ZMod 2] W)} {WB : Submodule (ZMod 2) W}
    (h : TransvConfig Sg Gg Tg Vg WB) (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    (hA : A = algOf Sg) (X : Submodule A W) [IsSimpleModule A X] (hXWB : ∀ x ∈ X, x ∈ WB)
    (hcard : Nat.card ↥X = 2 ∨
      (Nat.card ↥X = 16 ∧ ∃ a ∈ A, ∃ b ∈ A, ∃ x ∈ X, a (b x) ≠ b (a x))) :
    ∃ (d : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2)
      (φ : ↥Gg →* GL (Fin d) E),
      (Nat.card E = 2 ∨ Nat.card E = 4) ∧ Function.Injective φ ∧
      (∀ x : ↥Gg, LinearMap.ker (s9P1 (((x : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W))) = ⊥ ↔
        (s9P1 ((φ x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)).det ≠ 0) ∧
      (∀ g : ↥Gg, g ≠ 1 →
        (∃ v ∈ Vg, ∃ x ∈ Gg ⊔ Tg, (g : W ≃ₗ[ZMod 2] W) = x * v * x⁻¹) →
          IsTransvectionK (φ g : GL (Fin d) E)) := by
  have hdim : Nat.card ↥X = 2 ∨ Nat.card ↥X = 16 :=
    hcard.elim Or.inl fun hh => Or.inr hh.1
  have htop : isotypicComponent A W X = ⊤ := isotypicComponent_eq_top A hA h X hXWB
  have hss : IsSemisimpleModule A W := by
    refine isSemisimpleModule_of_isSemisimpleModule_submodule
      (s := {isotypicComponent A W ↥X}) (p := fun c => c) ?_ ?_
    · intro c hc
      obtain rfl := Set.mem_singleton_iff.mp hc
      exact inferInstance
    · simpa using htop
  have hiso : IsIsotypicOfType A W ↥X := IsIsotypicOfType.of_isotypicComponent_eq_top htop
  haveI : Module.Finite A W := Module.Finite.of_finite
  obtain ⟨d, ⟨ε⟩⟩ := hiso.linearEquiv_fun
  have hG' : ∀ g ∈ Gg, ∀ a ∈ A,
      (g : Module.End (ZMod 2) W) * a = a * (g : Module.End (ZMod 2) W) := by
    intro g hg
    have hf : ∀ s ∈ Sg, (g : Module.End (ZMod 2) W) * (s : Module.End (ZMod 2) W) =
        (s : Module.End (ZMod 2) W) * (g : Module.End (ZMod 2) W) := by
      intro s hs
      ext y
      exact congrArg (fun e : W ≃ₗ[ZMod 2] W => e y) (h.comm g hg s hs)
    rw [hA]
    exact commute_of_commute_gens Sg hf
  have htr : ∀ g : ↥Gg, g ≠ 1 →
      (∃ v ∈ Vg, ∃ x ∈ Gg ⊔ Tg, (g : W ≃ₗ[ZMod 2] W) = x * v * x⁻¹) →
        IsTransvectionK (s9rPhi A (RingEquiv.refl (Module.End A X)) ε Gg hG' g :
          GL (Fin d) (Module.End A X)) := by
    rintro ⟨g, hg⟩ hne ⟨v, hv, x, hx, hgv⟩
    subst hgv
    obtain ⟨hsq, Θ, hΘ, hθ⟩ :=
      transv_of_conj A hA h X hXWB hdim htop (x * v * x⁻¹) hg ⟨v, hv, x, hx, rfl⟩
        (fun h1 => hne (Subtype.ext h1))
    exact s9r_transv_phi A (RingEquiv.refl (Module.End A X)) ε Gg hG' ⟨x * v * x⁻¹, hg⟩ hne hsq
      ⟨Θ, hΘ, hθ⟩
  exact ⟨d, Module.End A X, endField A X, endFinite A X, charP_two_end A X,
    s9rPhi A (RingEquiv.refl (Module.End A X)) ε Gg hG', card_end_le A X hcard,
    s9r_inj_phi A (RingEquiv.refl (Module.End A X)) ε Gg hG',
    fun g => s9r_bridge A (RingEquiv.refl (Module.End A X)) ε Gg hG' g, htr⟩

theorem nk_rep_main {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {Sg Gg Tg Vg : Subgroup (W ≃ₗ[ZMod 2] W)} {WB : Submodule (ZMod 2) W}
    (h : TransvConfig Sg Gg Tg Vg WB) :
    ∃ (d : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2)
      (φ : ↥Gg →* GL (Fin d) E),
      (Nat.card E = 2 ∨ Nat.card E = 4) ∧ Function.Injective φ ∧
      (∀ x : ↥Gg, LinearMap.ker (s9P1 (((x : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W))) = ⊥ ↔
        (s9P1 ((φ x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)).det ≠ 0) ∧
      (∀ g : ↥Gg, g ≠ 1 →
        (∃ v ∈ Vg, ∃ x ∈ Gg ⊔ Tg, (g : W ≃ₗ[ZMod 2] W) = x * v * x⁻¹) →
          IsTransvectionK (φ g : GL (Fin d) E)) := by
  classical
  have hWB : WB ≠ ⊥ := by
    obtain ⟨v, hv, hv1⟩ := h.V_ne
    obtain ⟨w, hw⟩ : ∃ w : W, v w ≠ w := by
      by_contra hcon
      exact hv1 (LinearEquiv.ext fun w => by
        by_contra hw
        exact hcon ⟨w, hw⟩)
    intro hbot
    apply hw
    have hmem : v w - w ∈ WB := h.WB_V v hv w
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem
  have hex : ∃ n : ℕ, ∃ P : Submodule (ZMod 2) W,
      P ≤ WB ∧ P ≠ ⊥ ∧ InvUnder Sg P ∧ Module.finrank (ZMod 2) P = n :=
    ⟨_, WB, le_rfl, hWB, h.hb.inv, rfl⟩
  obtain ⟨P, hPle, hPne, hPinv, hPn⟩ := Nat.find_spec hex
  have hPmin : ∀ Q : Submodule (ZMod 2) W, Q ≤ P → InvUnder Sg Q → Q = ⊥ ∨ Q = P := by
    intro Q hQP hQinv
    by_cases hQ0 : Q = ⊥
    · exact Or.inl hQ0
    · right
      by_contra hne
      have hlt : Q < P := lt_of_le_of_ne hQP hne
      have hfin : Module.finrank (ZMod 2) Q < Module.finrank (ZMod 2) P :=
        Submodule.finrank_lt_finrank_of_lt hlt
      have hmin : Nat.find hex ≤ Module.finrank (ZMod 2) Q :=
        Nat.find_min' hex ⟨Q, hQP.trans hPle, hQ0, hQinv, rfl⟩
      omega
  haveI hsimp : IsSimpleModule (algOf Sg) ↥(toSubmoduleA Sg P hPinv) :=
    nk_isSimple hPne hPinv hPmin
  have hXc : Nat.card ↥(toSubmoduleA Sg P hPinv) = Nat.card ↥P :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have hPcard : Nat.card ↥P = 2 ^ Module.finrank (ZMod 2) P := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcard : Nat.card ↥(toSubmoduleA Sg P hPinv) = 2 ∨
      (Nat.card ↥(toSubmoduleA Sg P hPinv) = 16 ∧ ∃ a ∈ algOf Sg, ∃ b ∈ algOf Sg,
        ∃ x ∈ toSubmoduleA Sg P hPinv, a (b x) ≠ b (a x)) := by
    rcases h.hb.irr P hPle hPne hPinv hPmin with h1 | ⟨h4, s, hs, s', hs', w, hwP, hsw⟩
    · left
      rw [hXc, hPcard, h1, pow_one]
    · right
      refine ⟨by rw [hXc, hPcard, h4] <;> norm_num, ?_⟩
      exact ⟨(s : Module.End (ZMod 2) W), mem_algOf_of_mem Sg hs,
        (s' : Module.End (ZMod 2) W), mem_algOf_of_mem Sg hs', w, hwP, hsw⟩
  exact nk_rep_aux h (algOf Sg) rfl (toSubmoduleA Sg P hPinv) (fun x hx => hPle hx) hcard

theorem nk_star_bound {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {Sg Gg Tg Vg : Subgroup (W ≃ₗ[ZMod 2] W)} {WB : Submodule (ZMod 2) W}
    (h : TransvConfig Sg Gg Tg Vg WB) (v g : W ≃ₗ[ZMod 2] W) (hv : v ∈ Vg) (hg : g ∈ Gg) :
    (v * g * v⁻¹ * g⁻¹) ^ 3 = 1 ∨ (v * g * v⁻¹ * g⁻¹) ^ 4 = 1 ∨
      (v * g * v⁻¹ * g⁻¹) ^ 5 = 1 := by
  obtain ⟨d, E, hF, hfin, hch, φ, hE, hinj, -, htr⟩ := nk_rep_main h
  have hvG : v ∈ Gg := h.V_le hv
  set vG : ↥Gg := ⟨v, hvG⟩ with hvG_def
  set gG : ↥Gg := ⟨g, hg⟩ with hgG_def
  have hvv : vG * vG = 1 := Subtype.ext (h.V_sq v hv)
  have ht : (((φ vG : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) - 1) *
        (((φ vG : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) - 1) = 0 ∧
      (((φ vG : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) - 1).rank ≤ 1 := by
    by_cases h1 : vG = 1
    · rw [h1, map_one]
      simp
    · obtain ⟨-, hsq, hrk⟩ := htr vG h1 ⟨v, hv, 1, Subgroup.one_mem _, by simp [hvG_def]⟩
      exact ⟨hsq, hrk.le⟩
  have key := transvection_mul_conj_pow hE (φ vG) (φ gG)⁻¹ ht.1 ht.2
  have hyG : φ (vG * gG * vG⁻¹ * gG⁻¹) = φ vG * ((φ gG)⁻¹⁻¹ * φ vG * (φ gG)⁻¹) := by
    have hinv : (φ vG)⁻¹ = φ vG := by
      rw [← map_inv, inv_eq_of_mul_eq_one_right hvv]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hinv, inv_inv]
    group
  have hpow : ∀ m : ℕ, (φ vG * ((φ gG)⁻¹⁻¹ * φ vG * (φ gG)⁻¹)) ^ m = 1 →
      (v * g * v⁻¹ * g⁻¹) ^ m = 1 := by
    intro m hm
    rw [← hyG, ← map_pow] at hm
    have := congrArg Subtype.val (hinj (hm.trans (map_one φ).symm))
    simpa using this
  rcases key with h3 | h4 | h5
  · exact Or.inl (hpow 3 h3)
  · exact Or.inr (Or.inl (hpow 4 h4))
  · exact Or.inr (Or.inr (hpow 5 h5))

end CFSG.Quasithin.H13.L829NK
