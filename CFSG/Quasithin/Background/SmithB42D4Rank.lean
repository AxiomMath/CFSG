module

public import CFSG.Quasithin.Background.SmithB42D4Coord
public import CFSG.Sporadic.Schreier.J4SSylow

public section

namespace CFSG.Quasithin.B42D4

theorem card_mul_card_orth_le {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [Module.Finite F V] (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate) (S : AddSubgroup V) :
    Nat.card S * Nat.card {d : V // ∀ s ∈ S, B s d = 0} ≤ Nat.card V := by
  classical
  have : Finite V := Module.finite_of_finite F
  set W := Submodule.span F (S : Set V) with hW
  have hD : ∀ d : V, (∀ s ∈ S, B s d = 0) ↔ d ∈ B.orthogonal W := by
    intro d
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h n hn
      induction hn using Submodule.span_induction with
      | mem x hx => exact h x hx
      | zero => simp
      | add x y _ _ hx hy =>
        change B x d = 0 at hx
        change B y d = 0 at hy
        rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
      | smul c x _ hx =>
        change B (c • x) d = 0
        change B x d = 0 at hx
        rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
    · intro h s hs
      exact h s (Submodule.subset_span hs)
  have e1 : Nat.card {d : V // ∀ s ∈ S, B s d = 0} = Nat.card (B.orthogonal W) :=
    Nat.card_congr (Equiv.subtypeEquivRight hD)
  have e2 : Nat.card S ≤ Nat.card W := by
    refine Nat.card_le_card_of_injective (fun s => ⟨s, Submodule.subset_span s.2⟩) ?_
    intro a b h
    exact Subtype.ext (congrArg (fun x : W => (x : V)) h)
  have hfin := LinearMap.BilinForm.finrank_orthogonal hB W
  have hle : Module.finrank F W ≤ Module.finrank F V := Submodule.finrank_le W
  rw [e1]
  calc Nat.card S * Nat.card (B.orthogonal W) ≤ Nat.card W * Nat.card (B.orthogonal W) :=
        Nat.mul_le_mul_right _ e2
    _ = Nat.card V := by
      rw [Module.natCard_eq_pow_finrank (K := F) (V := W),
        Module.natCard_eq_pow_finrank (K := F) (V := B.orthogonal W),
        Module.natCard_eq_pow_finrank (K := F) (V := V), ← pow_add, hfin]
      congr 1
      omega

theorem card_eq_range_mul_ker {G H : Type*} [Group G] [Finite G] [Group H] (φ : G →* H) :
    Nat.card G = Nat.card φ.range * Nat.card φ.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]

theorem card_toAddSubgroup' {A : Type*} [AddCommGroup A] (T : Subgroup (Multiplicative A)) :
    Nat.card (Subgroup.toAddSubgroup' T) = Nat.card T :=
  Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun _ => Iff.rfl))

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

section Field

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

omit hσ3 in
theorem tr_of_fixed {x : K} (hx : σ x = x) : tr σ x = x := by
  rw [tr, hx, hx]; ring2

include hσ3 in
theorem c_eq_zero_of_conds {s c d : K} (hs : s ≠ 0) (hB : bF σ s c = 0)
    (h5 : e5F σ s c + tr σ (s * d) = 0) (hdc : tr σ (d * c) = 0) :
    c = 0 ∧ tr σ (s * d) = 0 := by
  have h3 := sigma_sigma_sigma σ hσ3
  set γ := c / s with hγdef
  have hc : c = s * γ := by rw [hγdef, mul_div_cancel₀ _ hs]
  have hs1 : σ s ≠ 0 := (map_ne_zero σ).2 hs
  have hs2 : σ (σ s) ≠ 0 := (map_ne_zero σ).2 hs1
  have hγ : σ γ = γ := by
    simp only [bF, hc, map_mul] at hB
    have h1 : σ s * σ (σ s) * (σ (σ γ) + σ γ) = 0 := by linear_combination hB
    have h2 : σ (σ γ) + σ γ = 0 :=
      (mul_eq_zero.1 h1).resolve_left (mul_ne_zero hs1 hs2)
    have h4 : σ (σ γ) = σ γ := by linear_combination (norm := ring2) h2
    have h5 := congrArg σ h4
    rw [h3, h4] at h5
    exact h5.symm
  have hN : σ (nK σ s) = nK σ s := sigma_nK σ hσ3 s
  have he5 : e5F σ s c = nK σ s * γ := by
    simp only [e5F, hc, map_mul, hγ]
    have : s * σ s * (σ (σ s) * γ) = nK σ s * γ := by rw [nK]; ring
    rw [this, tr_of_fixed σ (by rw [map_mul, hN, hγ])]
  have hsd : tr σ (s * d) = nK σ s * γ := by linear_combination (norm := ring2) h5 - he5
  have hdc' : tr σ (d * c) = γ * tr σ (s * d) := by
    simp only [hc, tr, map_mul, hγ]
    ring
  rw [hdc', hsd] at hdc
  have hN0 : nK σ s ≠ 0 := by
    rw [nK]; exact mul_ne_zero (mul_ne_zero hs hs1) hs2
  have hγ0 : γ = 0 := by
    have : nK σ s * (γ * γ) = 0 := by linear_combination hdc
    exact mul_self_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hN0)
  exact ⟨by rw [hc, hγ0, mul_zero], by rw [hsd, hγ0, mul_zero]⟩

@[expose] noncomputable def pairForm :
    LinearMap.BilinForm (trialityFixedField K σ.toRingHom) (trialityFixedField K σ.toRingHom × K) :=
  (LinearMap.mul (trialityFixedField K σ.toRingHom) (trialityFixedField K σ.toRingHom)).compl₁₂
      (LinearMap.fst _ _ _) (LinearMap.fst _ _ _) +
    (trialityTraceForm K σ.toRingHom hσ3).compl₁₂ (LinearMap.snd _ _ _) (LinearMap.snd _ _ _)

omit [CharP K 2] in
theorem pairForm_apply (x y : trialityFixedField K σ.toRingHom × K) :
    pairForm σ hσ3 x y = x.1 * y.1 + trialityTrace K σ.toRingHom hσ3 (x.2 * y.2) := rfl

theorem pairForm_nondegenerate : (pairForm σ hσ3).Nondegenerate := by
  have hT := trialityTraceForm_nondegenerate K σ.toRingHom hσ3
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h1 := hx (1, 0)
    rw [pairForm_apply, mul_zero, mul_one] at h1
    have h0 : trialityTrace K σ.toRingHom hσ3 0 = 0 := Subtype.ext (by
      rw [coe_trialityTrace]; simp)
    rw [h0, add_zero] at h1
    have h2 : x.2 = 0 := hT.1 x.2 fun t => by
      have := hx (0, t)
      rw [pairForm_apply, mul_zero, zero_add] at this
      exact this
    exact Prod.ext h1 h2
  · have h1 := hy (1, 0)
    rw [pairForm_apply, zero_mul, one_mul] at h1
    have h0 : trialityTrace K σ.toRingHom hσ3 0 = 0 := Subtype.ext (by
      rw [coe_trialityTrace]; simp)
    rw [h0, add_zero] at h1
    have h2 : y.2 = 0 := hT.2 y.2 fun t => by
      have := hy (0, t)
      rw [pairForm_apply, zero_mul, zero_add] at this
      exact this
    exact Prod.ext h1 h2

omit [CharP K 2] in
include hσ3 in
theorem tr_eq_coe_trace (x : K) : tr σ x = (trialityTrace K σ.toRingHom hσ3 x : K) := by
  rw [coe_trialityTrace]; rfl

end Field

section ACoord


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "UU" => graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom

include hσ3 in
theorem exists_ox₁_mul_Q0 {u : ModGL TwistTag.D4.tag K} (hu : u ∈ UU) :
    ∃ a : K, ∃ g ∈ Q0 σ, u = ox₁ σ a * g := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := (mem_U_iff σ hσ3).1 hu
  exact ⟨a, _, qE_mem_Q0 σ hσ3 b c d e f, rfl⟩

include hσ3 in
theorem eq_of_ox₁_mul_Q0 {a a' : K} {g g' : ModGL TwistTag.D4.tag K} (hg : g ∈ Q0 σ)
    (hg' : g' ∈ Q0 σ) (h : ox₁ σ a * g = ox₁ σ a' * g') : a = a' := by
  obtain ⟨b, c, d, e, f, rfl⟩ := (mem_Q0_iff' σ hσ3).1 hg
  obtain ⟨b', c', d', e', f', rfl⟩ := (mem_Q0_iff' σ hσ3).1 hg'
  exact (uE_inj σ hσ3 h).1

@[expose] noncomputable def aCoord (u : UU) : K :=
  Classical.choose (exists_ox₁_mul_Q0 σ hσ3 u.2)

theorem aCoord_spec (u : UU) : ∃ g ∈ Q0 σ, (u : ModGL TwistTag.D4.tag K) =
    ox₁ σ (aCoord σ hσ3 u) * g :=
  Classical.choose_spec (exists_ox₁_mul_Q0 σ hσ3 u.2)

theorem aCoord_eq {u : UU} {a : K} {g : ModGL TwistTag.D4.tag K} (hg : g ∈ Q0 σ)
    (h : (u : ModGL TwistTag.D4.tag K) = ox₁ σ a * g) : aCoord σ hσ3 u = a := by
  obtain ⟨g', hg', hu⟩ := aCoord_spec σ hσ3 u
  exact eq_of_ox₁_mul_Q0 σ hσ3 hg' hg (hu.symm.trans h)

theorem aCoord_eq_zero_iff (u : UU) :
    aCoord σ hσ3 u = 0 ↔ (u : ModGL TwistTag.D4.tag K) ∈ Q0 σ := by
  obtain ⟨g, hg, hu⟩ := aCoord_spec σ hσ3 u
  constructor
  · intro h
    rw [hu, h, ox₁_zero σ hσ3, one_mul]
    exact hg
  · intro h
    exact aCoord_eq σ hσ3 h (by rw [ox₁_zero σ hσ3, one_mul])

@[expose] noncomputable def qCoord (g : Q0 σ) :
    trialityFixedField K τ₀ × K × K × trialityFixedField K τ₀ × trialityFixedField K τ₀ :=
  let h := (mem_Q0_iff' σ hσ3).1 g.2
  (Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose (Classical.choose_spec (Classical.choose_spec h)),
    Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))),
    Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec h)))))

theorem qCoord_spec (g : Q0 σ) :
    (g : ModGL TwistTag.D4.tag K) = qE σ (qCoord σ hσ3 g).1 (qCoord σ hσ3 g).2.1
      (qCoord σ hσ3 g).2.2.1 (qCoord σ hσ3 g).2.2.2.1 (qCoord σ hσ3 g).2.2.2.2 :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec ((mem_Q0_iff' σ hσ3).1 g.2)))))

theorem qCoord_eq {g : Q0 σ} {b : trialityFixedField K τ₀} {c d : K}
    {e f : trialityFixedField K τ₀} (h : (g : ModGL TwistTag.D4.tag K) = qE σ b c d e f) :
    qCoord σ hσ3 g = (b, c, d, e, f) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := qE_inj σ hσ3 ((qCoord_spec σ hσ3 g).symm.trans h)
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 h5)))

end ACoord

section AHom


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "UU" => graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom

theorem aCoord_mul (u v : UU) : aCoord σ hσ3 (u * v) = aCoord σ hσ3 u + aCoord σ hσ3 v := by
  obtain ⟨g, hg, hu⟩ := aCoord_spec σ hσ3 u
  obtain ⟨g', hg', hv⟩ := aCoord_spec σ hσ3 v
  refine aCoord_eq σ hσ3 (mul_mem (conj_ox₁_mem_Q0 σ hσ3 (aCoord σ hσ3 v) hg) hg') ?_
  rw [Subgroup.coe_mul, hu, hv, ox₁_add σ hσ3]
  have hinv := ox₁_inv σ hσ3 (aCoord σ hσ3 v)
  rw [hinv]
  have h2 := ox₁_mul_self σ hσ3 (aCoord σ hσ3 v)
  calc ox₁ σ (aCoord σ hσ3 u) * g * (ox₁ σ (aCoord σ hσ3 v) * g') =
      ox₁ σ (aCoord σ hσ3 u) * (ox₁ σ (aCoord σ hσ3 v) * ox₁ σ (aCoord σ hσ3 v)) * g *
        ox₁ σ (aCoord σ hσ3 v) * g' := by rw [h2, mul_one]; group
    _ = _ := by group

@[expose] noncomputable def aHom : UU →* Multiplicative K where
  toFun u := Multiplicative.ofAdd (aCoord σ hσ3 u)
  map_one' := by
    rw [(aCoord_eq_zero_iff σ hσ3 1).2 (Subgroup.one_mem _), ofAdd_zero]
  map_mul' u v := by rw [aCoord_mul, ofAdd_add]

theorem qE_mul_k (b : trialityFixedField K τ₀) (c d : K) (e f b' : trialityFixedField K τ₀)
    (c' d' : K) (e' f' : trialityFixedField K τ₀) :
    qE σ b c d e f * qE σ b' c' d' e' f' =
      qE σ (b + b' : trialityFixedField K τ₀) (c + c') (d + d') (e + e' : trialityFixedField K τ₀)
        (trialityTrace K τ₀ hσ3 (d * c') + e * b' + f + f' : trialityFixedField K τ₀) := by
  rw [qE_mul σ hσ3]
  refine qE_congr σ ?_ rfl rfl ?_ ?_
  · exact (Subfield.coe_add _ _ _).symm
  · exact (Subfield.coe_add _ _ _).symm
  · rw [Subfield.coe_add, Subfield.coe_add, Subfield.coe_add, Subfield.coe_mul,
      coe_trialityTrace]
    rfl

@[expose] noncomputable def bcHom : Q0 σ →* Multiplicative (trialityFixedField K τ₀ × K) where
  toFun g := Multiplicative.ofAdd ((qCoord σ hσ3 g).1, (qCoord σ hσ3 g).2.1)
  map_one' := by
    have h1 : ((1 : Q0 σ) : ModGL TwistTag.D4.tag K) = qE σ (0 : trialityFixedField K τ₀) 0 0
        (0 : trialityFixedField K τ₀) (0 : trialityFixedField K τ₀) := by
      simp [qE, pinnedX_zero, ox₃_zero', ox₄_zero']
    rw [qCoord_eq σ hσ3 h1]
    rfl
  map_mul' g g' := by
    have h := qE_mul_k σ hσ3 (qCoord σ hσ3 g).1 (qCoord σ hσ3 g).2.1 (qCoord σ hσ3 g).2.2.1
      (qCoord σ hσ3 g).2.2.2.1 (qCoord σ hσ3 g).2.2.2.2 (qCoord σ hσ3 g').1
      (qCoord σ hσ3 g').2.1 (qCoord σ hσ3 g').2.2.1 (qCoord σ hσ3 g').2.2.2.1
      (qCoord σ hσ3 g').2.2.2.2
    rw [← qCoord_spec, ← qCoord_spec] at h
    rw [qCoord_eq σ hσ3 (by rw [Subgroup.coe_mul]; exact h)]
    rfl

theorem card_ker_le {E : Subgroup (ModGL TwistTag.D4.tag K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1)
    (S : AddSubgroup K) (hS : ∀ s ∈ S, ∃ y ∈ E, ∃ g ∈ Q0 σ, y = ox₁ σ s * g)
    {s₀ : K} (hs₀S : s₀ ∈ S) (hs₀ : s₀ ≠ 0) :
    Nat.card (E ⊓ Q0 σ : Subgroup _) ≤ Nat.card {d : K // ∀ s ∈ S,
      trialityTraceForm K τ₀ hσ3 s d = 0} *
        Nat.card (trialityFixedField K τ₀) * Nat.card (trialityFixedField K τ₀) := by
  classical
  have hcond : ∀ x : (E ⊓ Q0 σ : Subgroup _),
      ((qCoord σ hσ3 ⟨x, x.2.2⟩).1 : K) = 0 ∧ (qCoord σ hσ3 ⟨x, x.2.2⟩).2.1 = 0 ∧
        ∀ s ∈ S, tr σ (s * (qCoord σ hσ3 ⟨x, x.2.2⟩).2.2.1) = 0 := by
    intro x
    set q := qCoord σ hσ3 ⟨x, x.2.2⟩ with hq
    have hx : (x : ModGL TwistTag.D4.tag K) = qE σ q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 :=
      qCoord_spec σ hσ3 ⟨x, x.2.2⟩
    have hsqx := hsq x x.2.1
    rw [hx, qE_mul_self_eq_one_iff σ hσ3] at hsqx
    have conds : ∀ s ∈ S, s ≠ 0 → ((q.1 : K) = 0 ∧ bF σ s q.2.1 = 0 ∧
        e5F σ s q.2.1 + tr σ (s * q.2.2.1) = 0) := by
      intro s hs hs0
      obtain ⟨y, hyE, g, hg, rfl⟩ := hS s hs
      obtain ⟨b₀, c₀, d₀, e₀, f₀, rfl⟩ := (mem_Q0_iff' σ hσ3).1 hg
      have hc := hcomm _ hyE x x.2.1
      rw [hx] at hc
      exact commute_ox₁_conds σ hσ3 hs0 b₀ c₀ d₀ e₀ f₀ q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 hc
    obtain ⟨hb, hB, h5⟩ := conds s₀ hs₀S hs₀
    rw [hb, mul_zero, add_zero] at hsqx
    obtain ⟨hc0, -⟩ := c_eq_zero_of_conds σ hσ3 hs₀ hB h5 hsqx
    refine ⟨hb, hc0, fun s hs => ?_⟩
    by_cases hs0 : s = 0
    · rw [hs0, zero_mul, tr]; simp
    · obtain ⟨-, hB', h5'⟩ := conds s hs hs0
      exact (c_eq_zero_of_conds σ hσ3 hs0 hB' h5' hsqx).2
  let F : (E ⊓ Q0 σ : Subgroup _) → {d : K // ∀ s ∈ S, trialityTraceForm K τ₀ hσ3 s d = 0} ×
      trialityFixedField K τ₀ × trialityFixedField K τ₀ := fun x =>
    (⟨(qCoord σ hσ3 ⟨x, x.2.2⟩).2.2.1, fun s hs => Subtype.ext (by
      rw [trialityTraceForm_apply, ← tr_eq_coe_trace σ hσ3]
      exact (hcond x).2.2 s hs)⟩,
      (qCoord σ hσ3 ⟨x, x.2.2⟩).2.2.2.1, (qCoord σ hσ3 ⟨x, x.2.2⟩).2.2.2.2)
  have hF : Function.Injective F := by
    intro x x' hxx
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hxx
    obtain ⟨hd, he, hf⟩ := hxx
    have hx := qCoord_spec σ hσ3 ⟨x, x.2.2⟩
    have hx' := qCoord_spec σ hσ3 ⟨x', x'.2.2⟩
    have hb : (qCoord σ hσ3 ⟨x, x.2.2⟩).1 = (qCoord σ hσ3 ⟨x', x'.2.2⟩).1 :=
      Subtype.ext ((hcond x).1.trans (hcond x').1.symm)
    have hc : (qCoord σ hσ3 ⟨x, x.2.2⟩).2.1 = (qCoord σ hσ3 ⟨x', x'.2.2⟩).2.1 :=
      (hcond x).2.1.trans (hcond x').2.1.symm
    apply Subtype.ext
    rw [hx, hx', hb, hc, hd, he, hf]
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_prod, ← mul_assoc] at this

include hσ3 in
theorem card_le_of_le_Q0 {E : Subgroup (ModGL TwistTag.D4.tag K)} (hEQ : E ≤ Q0 σ)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card E ≤ Nat.card (trialityFixedField K τ₀ × K) * Nat.card (trialityFixedField K τ₀) := by
  classical
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set ψ := (bcHom σ hσ3).comp (Subgroup.inclusion hEQ) with hψ
  set T₁ := Subgroup.toAddSubgroup' ψ.range with hT₁
  have hcard := card_eq_range_mul_ker ψ
  rw [← card_toAddSubgroup'] at hcard
  have hker : ∀ x : ψ.ker, (qCoord σ hσ3 ⟨x, hEQ x.1.2⟩).1 = 0 ∧
      (qCoord σ hσ3 ⟨x, hEQ x.1.2⟩).2.1 = 0 := by
    intro x
    have h := x.2
    rw [MonoidHom.mem_ker] at h
    have h' := congrArg Multiplicative.toAdd h
    simp only [hψ, MonoidHom.comp_apply, bcHom, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_ofAdd, toAdd_one] at h'
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  have horth : ∀ x : ψ.ker, ∀ t ∈ T₁, pairForm σ hσ3 t
      ((qCoord σ hσ3 ⟨x, hEQ x.1.2⟩).2.2.2.1, (qCoord σ hσ3 ⟨x, hEQ x.1.2⟩).2.2.1) = 0 := by
    intro x t ht
    rw [Subgroup.mem_toAddSubgroup'] at ht
    obtain ⟨y, hy⟩ := ht
    have hy' := congrArg Multiplicative.toAdd hy
    simp only [hψ, MonoidHom.comp_apply, bcHom, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_ofAdd] at hy'
    have hx := qCoord_spec σ hσ3 ⟨x, hEQ x.1.2⟩
    have hyy := qCoord_spec σ hσ3 ⟨y, hEQ y.2⟩
    have hc := hcomm x x.1.2 y y.2
    change (x : ModGL TwistTag.D4.tag K) * y = y * x at hc
    rw [hx, hyy, qE_commute_iff σ hσ3] at hc
    obtain ⟨hb0, hc0⟩ := hker x
    rw [hb0, hc0] at hc
    simp only [ZeroMemClass.coe_zero, mul_zero, add_zero] at hc
    have ht1 : t.1 = (qCoord σ hσ3 ⟨y, hEQ y.2⟩).1 := (congrArg Prod.fst hy').symm
    have ht2 : t.2 = (qCoord σ hσ3 ⟨y, hEQ y.2⟩).2.1 := (congrArg Prod.snd hy').symm
    apply Subtype.ext
    rw [pairForm_apply, Subfield.coe_add, Subfield.coe_mul, ← tr_eq_coe_trace σ hσ3, ht1, ht2]
    rw [tr, tr, map_zero, map_zero, add_zero, add_zero] at hc
    simp only [tr, ZeroMemClass.coe_zero]
    linear_combination (norm := ring2) hc
  let F : ψ.ker → {z : trialityFixedField K τ₀ × K // ∀ t ∈ T₁, pairForm σ hσ3 t z = 0} ×
      trialityFixedField K τ₀ := fun x =>
    (⟨((qCoord σ hσ3 ⟨x, hEQ x.1.2⟩).2.2.2.1, (qCoord σ hσ3 ⟨x, hEQ x.1.2⟩).2.2.1),
      fun t ht => horth x t ht⟩, (qCoord σ hσ3 ⟨x, hEQ x.1.2⟩).2.2.2.2)
  have hF : Function.Injective F := by
    intro x x' hxx
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hxx
    obtain ⟨⟨he, hd⟩, hf⟩ := hxx
    have hx := qCoord_spec σ hσ3 ⟨x, hEQ x.1.2⟩
    have hx' := qCoord_spec σ hσ3 ⟨x', hEQ x'.1.2⟩
    have hb := (hker x).1.trans (hker x').1.symm
    have hc := (hker x).2.trans (hker x').2.symm
    apply Subtype.ext; apply Subtype.ext
    rw [hx, hx', hb, hc, hd, he, hf]
  have hinj := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod] at hinj
  have hA := card_mul_card_orth_le (pairForm σ hσ3) (pairForm_nondegenerate σ hσ3) T₁
  rw [hcard]
  calc Nat.card T₁ * Nat.card ψ.ker ≤ Nat.card T₁ *
        (Nat.card {z : trialityFixedField K τ₀ × K // ∀ t ∈ T₁, pairForm σ hσ3 t z = 0} *
          Nat.card (trialityFixedField K τ₀)) := Nat.mul_le_mul_left _ hinj
    _ = Nat.card T₁ *
        Nat.card {z : trialityFixedField K τ₀ × K // ∀ t ∈ T₁, pairForm σ hσ3 t z = 0} *
          Nat.card (trialityFixedField K τ₀) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hA

include hσ3 in
theorem card_le_of_elemAbelian_U (hK : Nat.card K = Nat.card (trialityFixedField K τ₀) ^ 3)
    {E : Subgroup (ModGL TwistTag.D4.tag K)} (hEU : E ≤ UU)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ Nat.card (trialityFixedField K τ₀) ^ 5 := by
  classical
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set q := Nat.card (trialityFixedField K τ₀) with hq
  set φ := (aHom σ hσ3).comp (Subgroup.inclusion hEU) with hφ
  set S := Subgroup.toAddSubgroup' φ.range with hSdef
  have hcard := card_eq_range_mul_ker φ
  rw [← card_toAddSubgroup'] at hcard
  have hφx : ∀ x : E, Multiplicative.toAdd (φ x) = aCoord σ hσ3 ⟨x, hEU x.2⟩ := fun x => rfl
  have hkerQ : ∀ x : E, x ∈ φ.ker ↔ (x : ModGL TwistTag.D4.tag K) ∈ Q0 σ := by
    intro x
    rw [MonoidHom.mem_ker, ← aCoord_eq_zero_iff σ hσ3 ⟨x, hEU x.2⟩, ← hφx]
    exact ⟨fun h => by rw [h]; rfl, fun h => by rw [← ofAdd_toAdd (φ x), h, ofAdd_zero]⟩
  have hker : Nat.card φ.ker = Nat.card (E ⊓ Q0 σ : Subgroup _) := by
    refine Nat.card_congr ⟨fun x => ⟨x, x.1.2, (hkerQ x.1).1 x.2⟩,
      fun y => ⟨⟨y, y.2.1⟩, (hkerQ ⟨y, y.2.1⟩).2 y.2.2⟩, fun x => rfl, fun y => rfl⟩
  have hmemS : ∀ s : K, s ∈ S ↔ ∃ x : E, aCoord σ hσ3 ⟨x, hEU x.2⟩ = s := by
    intro s
    rw [Subgroup.mem_toAddSubgroup']
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [← hφx, hx, toAdd_ofAdd]⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [← hx, ← hφx, ofAdd_toAdd]⟩
  by_cases hS : ∃ s ∈ S, s ≠ 0
  · obtain ⟨s₀, hs₀S, hs₀⟩ := hS
    have hS' : ∀ s ∈ S, ∃ y ∈ E, ∃ g ∈ Q0 σ, y = ox₁ σ s * g := by
      intro s hs
      obtain ⟨x, rfl⟩ := (hmemS s).1 hs
      obtain ⟨g, hg, hx⟩ := aCoord_spec σ hσ3 ⟨x, hEU x.2⟩
      exact ⟨x, x.2, g, hg, hx⟩
    have hk := card_ker_le σ hσ3 hcomm hsq S hS' hs₀S hs₀
    have hA := card_mul_card_orth_le (trialityTraceForm K τ₀ hσ3)
      (trialityTraceForm_nondegenerate K τ₀ hσ3) S
    rw [hcard, hker]
    calc Nat.card S * Nat.card (E ⊓ Q0 σ : Subgroup _) ≤ Nat.card S *
          (Nat.card {d : K // ∀ s ∈ S, trialityTraceForm K τ₀ hσ3 s d = 0} * q * q) :=
          Nat.mul_le_mul_left _ hk
      _ = Nat.card S * Nat.card {d : K // ∀ s ∈ S, trialityTraceForm K τ₀ hσ3 s d = 0} *
          (q * q) := by ring
      _ ≤ Nat.card K * (q * q) := Nat.mul_le_mul_right _ hA
      _ = q ^ 5 := by rw [hK]; ring
  · push Not at hS
    have hEQ : E ≤ Q0 σ := by
      intro x hx
      have h0 := hS _ ((hmemS _).2 ⟨⟨x, hx⟩, rfl⟩)
      exact (aCoord_eq_zero_iff σ hσ3 ⟨x, hEU hx⟩).1 h0
    have h := card_le_of_le_Q0 σ hσ3 hEQ hcomm
    rw [Nat.card_prod, hK] at h
    calc Nat.card E ≤ q * q ^ 3 * q := h
      _ = q ^ 5 := by ring

include hσ3 in
theorem card_le_of_elemAbelian (hK : Nat.card K = Nat.card (trialityFixedField K τ₀) ^ 3)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K τ₀))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card E ≤ Nat.card (trialityFixedField K τ₀) ^ 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨P, hP⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow]; exact hsq x x.2)⟩
  obtain ⟨Q, hQ⟩ := hE2.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (graphFixedRootGroup TwistTag.D4 K τ₀) P Q
  rw [Sylow.coe_subgroup_smul, hP] at hQ
  have key : ∀ x ∈ E, ((g⁻¹ * x * g : graphFixedRootGroup TwistTag.D4 K τ₀) :
      ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hQ hx
    have hxy : g⁻¹ * x * g = y := by
      rw [← hyx]
      change g⁻¹ * (g * y * g⁻¹) * g = y
      group
    rw [hxy]
    exact hy
  set E' : Subgroup (ModGL TwistTag.D4.tag K) :=
    (E.map (MulAut.conj g⁻¹).toMonoidHom).map (graphFixedRootGroup TwistTag.D4 K τ₀).subtype
    with hE'
  have hcardE' : Nat.card E' = Nat.card E := by
    rw [hE', Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hE'U : E' ≤ graphFixedPosUnipotent TwistTag.D4 K τ₀ := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    convert key x hx using 1
    change ((g⁻¹ * x * g⁻¹⁻¹ : graphFixedRootGroup TwistTag.D4 K τ₀) : ModGL TwistTag.D4.tag K) =
      ((g⁻¹ * x * g : graphFixedRootGroup TwistTag.D4 K τ₀) : ModGL TwistTag.D4.tag K)
    rw [inv_inv]
  have hcomm' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    congr 1
    calc g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * (x * y) * g⁻¹⁻¹ := by group
      _ = g⁻¹ * (y * x) * g⁻¹⁻¹ := by rw [hcomm x hx y hy]
      _ = _ := by group
  have hsq' : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← sq, ← map_pow (MulAut.conj g⁻¹), hsq x hx, map_one]
    rfl
  rw [← hcardE']
  exact card_le_of_elemAbelian_U σ hσ3 hK hE'U hcomm' hsq'

end AHom

end CFSG.Quasithin.B42D4
