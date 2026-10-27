module

public import CFSG.Quasithin.MS93.S33DSp
public import CFSG.Quasithin.MS93.S33XMain
public import CFSG.Quasithin.MS93.S5Q2V

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Omega5

variable {F : Type} [Field F]

theorem sp4Quad_smul (c : F) (x : MSP.V4 F) : sp4Quad F (c • x) = c ^ 2 * sp4Quad F x := by
  simp only [sp4Quad, Pi.smul_apply, smul_eq_mul]
  ring

variable [CharP F 2]

theorem toAdd_omega5Act_mul_inv (g : MSP.Sp4 F) (x : MSP.V4 F) :
    Multiplicative.toAdd (omega5Act F g (Multiplicative.ofAdd (x, 0)) *
        (Multiplicative.ofAdd (x, 0))⁻¹) =
      (MSP.mat g *ᵥ x - x,
        sp4Quad F (MSP.mat g *ᵥ x - x) + MSP.form F x (MSP.mat g *ᵥ x - x)) := by
  rw [toAdd_mul, toAdd_inv, omega5Act_toAdd, toAdd_ofAdd]
  refine Prod.ext ?_ ?_
  · show MSP.mat g *ᵥ x + -x = MSP.mat g *ᵥ x - x
    rw [sub_eq_add_neg]
  · show 0 + sp4Quad F x + sp4Quad F (spMat g *ᵥ x) + -0 = _
    have h3 : sp4Quad F (spMat g *ᵥ x) = sp4Quad F x + sp4Quad F (MSP.mat g *ᵥ x - x) +
        MSP.form F x (MSP.mat g *ᵥ x - x) := by
      rw [form_eq_bil, ← sp4Quad_add]
      congr 1
      change MSP.mat g *ᵥ x = x + (MSP.mat g *ᵥ x - x)
      abel
    rw [h3]
    have h2 : sp4Quad F x + sp4Quad F x = 0 := CharTwo.add_self_eq_zero _
    linear_combination h2

theorem mem_omComm_xPoint_of_smul {p₀ : MSP.V4 F} (hp₀ : p₀ ≠ 0) (c : F) :
    Multiplicative.ofAdd (c • p₀, c ^ 2 * sp4Quad F p₀ + c) ∈ omComm (MSP.xPoint (F ∙ p₀)) := by
  obtain ⟨x, hx⟩ := MSP.exists_form_eq_one hp₀
  have hcomm : omega5Act F (MSP.transv p₀ c) (Multiplicative.ofAdd (x, 0)) *
      (Multiplicative.ofAdd (x, 0))⁻¹ ∈ omComm (MSP.xPoint (F ∙ p₀)) :=
    Subgroup.subset_closure ⟨_, MSP.transv_mem_xPoint p₀ c, _, rfl⟩
  have hval : omega5Act F (MSP.transv p₀ c) (Multiplicative.ofAdd (x, 0)) *
      (Multiplicative.ofAdd (x, 0))⁻¹ =
        Multiplicative.ofAdd (c • p₀, c ^ 2 * sp4Quad F p₀ + c) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, omega5Act_toAdd, toAdd_ofAdd, toAdd_ofAdd]
    have hm : spMat (MSP.transv p₀ c) *ᵥ x = x + c • p₀ := by
      change MSP.mat (MSP.transv p₀ c) *ᵥ x = _
      rw [MSP.transv_mulVec, hx, mul_one]
    rw [hm, sp4Quad_add]
    refine Prod.ext (by simp) ?_
    simp only [Prod.snd_add, Prod.snd_neg, neg_zero, add_zero, zero_add]
    have h1 : sp4Quad F (c • p₀) = c ^ 2 * sp4Quad F p₀ := sp4Quad_smul c p₀
    have h2 : JonesParshall.bil x (c • p₀) = c := by
      rw [← form_eq_bil, map_smul, smul_eq_mul, MSP.form_swap, hx, CharTwo.neg_eq, mul_one]
    rw [h1, h2]
    have h3 : sp4Quad F x + sp4Quad F x = 0 := CharTwo.add_self_eq_zero _
    linear_combination h3
  rw [← hval]
  exact hcomm

theorem omega5Act_mul_inv_eq_two (hsq : ∀ t : F, t ^ 2 = t) {p₀ c₀ x₀ x₁ : MSP.V4 F}
    {g g₀ : MSP.Sp4 F} (hpc : MSP.form F p₀ c₀ = 0) (hx₁p : MSP.form F p₀ x₁ = 1)
    (hx₁c : MSP.form F c₀ x₁ = MSP.form F c₀ x₀) (hc₀ : MSP.mat g₀ *ᵥ x₀ - x₀ = c₀)
    {a₁ b₁ : F} (hab : MSP.mat g *ᵥ x₁ - x₁ = a₁ • p₀ + b₁ • c₀) (ε : F) :
    omega5Act F g (Multiplicative.ofAdd (ε • x₁, 0)) * (Multiplicative.ofAdd (ε • x₁, 0))⁻¹ =
      Multiplicative.ofAdd ((ε * a₁) • p₀, (ε * a₁) ^ 2 * sp4Quad F p₀ + ε * a₁) *
        (omega5Act F g₀ (Multiplicative.ofAdd ((ε * b₁) • x₀, 0)) *
          (Multiplicative.ofAdd ((ε * b₁) • x₀, 0))⁻¹) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_omega5Act_mul_inv, toAdd_mul, toAdd_ofAdd, toAdd_omega5Act_mul_inv]
  have hv : MSP.mat g *ᵥ (ε • x₁) - ε • x₁ = ε • (a₁ • p₀ + b₁ • c₀) := by
    rw [Matrix.mulVec_smul, ← smul_sub, hab]
  have hv₀ : MSP.mat g₀ *ᵥ ((ε * b₁) • x₀) - (ε * b₁) • x₀ = (ε * b₁) • c₀ := by
    rw [Matrix.mulVec_smul, ← smul_sub, hc₀]
  rw [hv, hv₀]
  have h1 : MSP.form F x₁ p₀ = 1 := by rw [MSP.form_swap p₀ x₁, hx₁p, CharTwo.neg_eq]
  have h2 : MSP.form F x₁ c₀ = MSP.form F x₀ c₀ := by
    rw [MSP.form_swap c₀ x₁, hx₁c, ← MSP.form_swap c₀ x₀]
  have hε := hsq ε
  have hb := hsq b₁
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, smul_add, smul_smul]
  · simp only [Prod.snd_add, sp4Quad_smul, sp4Quad_add, ← form_eq_bil, map_add, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    linear_combination ε ^ 2 * a₁ * b₁ * hpc + ε ^ 2 * a₁ * h1 + ε ^ 2 * b₁ * h2 + a₁ * hε -
      ε ^ 2 * MSP.form F x₀ c₀ * hb

end Omega5

section Core

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {A : Subgroup G} {α : ↥A →* ↥(StatedSp 2 F)}
  {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → MSP.V4 F)}

variable (h : PUHyp M T L) (hAM : A ≤ M) (hβ : Function.Surjective β)
  (hβker : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L))
  (hAβ : ∀ a : ↥A, IsCoordAct β a (MSP.mat (α a)).mulVec)
include h hAM hβ hβker hAβ

theorem d_core [CharP F 2] {k : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card F = 2 ^ k) (hLA : L ≤ A)
    (hα : Function.Surjective α) (hCfix : ∀ a ∈ A, ∀ z ∈ Uq M T L ⊓ Zq M L, a * z * a⁻¹ = z)
    {F₀ Yq Aq : Subgroup G} (hF₀A : F₀ ≤ A) (hYqA : Yq ≤ A) {p₀ : MSP.V4 F} (hp₀ : p₀ ≠ 0)
    (hpF : (F₀.subgroupOf A).map α = MSP.xPoint (F ∙ p₀))
    (hAlo : Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G) ≤ Aq)
    (hYR : Yq ≤ Subgroup.centralizer ((⁅Uq M T L, F₀⁆ : Subgroup G) : Set G))
    (hAYY : ⁅⁅Aq, Yq⁆, Yq⁆ = ⊥) (hY : ¬ ⁅Uq M T L, Yq⁆ ≤ ⁅Uq M T L, F₀⁆ ⊔ ⁅Aq, Yq⁆) :
    2 ^ k ≤ Nat.card ↥⁅Aq, Yq⁆ ∧
      ∀ Z' : Subgroup G, Z' ≤ Zq M L → (∀ a ∈ A, ∀ z ∈ Z', a * z * a⁻¹ = z) →
        Aq ≤ (Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G)) ⊔ Z' →
        Nat.card ↥⁅Aq, Yq⁆ = 2 ^ k ∧ ⁅Aq, Yq⁆ ≤ ⁅Uq M T L, F₀⁆ ⊔ (Uq M T L ⊓ Zq M L) := by
  obtain ⟨ψ, hψs, hψe, hψZ⟩ :=
    exists_omega5_cover h hAM hβ hβker hAβ hk hcard hLA hα hCfix
  set p : Submodule F (MSP.V4 F) := F ∙ p₀ with hpdef
  have hp : MSP.IsPoint p := MSP.isPoint_span hp₀
  have hψ1 : ∀ w, ((ψ w : ↥(Uq M T L)) : G) = 1 → w ∈ omega5Rad F := fun w hw =>
    hψZ w (by rw [hw]; exact one_mem _)
  have hcψ : ∀ (y : ↥A) (w : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)),
      ⁅((ψ w : ↥(Uq M T L)) : G), (y : G)⁆ =
        ((ψ (omega5Act F (α y) w * w⁻¹)⁻¹ : ↥(Uq M T L)) : G) := by
    intro y w
    rw [map_inv, map_mul, map_inv, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv, hψe,
      commutatorElement_def]
    group
  have hfixX : ∀ {γ : MSP.Sp4 F}, γ ∈ MSP.xPoint p → ∀ x ∈ MSP.perp p, ∀ s : F,
      omega5Act F γ (Multiplicative.ofAdd (x, s)) = Multiplicative.ofAdd (x, s) := by
    intro γ hγ x hx s
    have hγx : MSP.mat γ *ᵥ x = x := hγ x hx
    apply Multiplicative.toAdd.injective
    rw [omega5Act_toAdd, toAdd_ofAdd]
    have hm : spMat γ *ᵥ x = x := hγx
    rw [hm]
    refine Prod.ext rfl ?_
    show s + sp4Quad F x + sp4Quad F x = s
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hUt : ∀ x ∈ MSP.perp p, ∀ s : F,
      ((ψ (Multiplicative.ofAdd (x, s)) : ↥(Uq M T L)) : G) ∈
        Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G) := by
    intro x hx s
    refine ⟨(ψ _).2, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
    have hγ : α ⟨f, hF₀A hf⟩ ∈ MSP.xPoint p := by
      rw [← hpF]
      exact ⟨⟨f, hF₀A hf⟩, Subgroup.mem_subgroupOf.2 hf, rfl⟩
    have h1 := hψe ⟨f, hF₀A hf⟩ (Multiplicative.ofAdd (x, s))
    rw [hfixX hγ x hx s] at h1
    have h2 : f * ((ψ (Multiplicative.ofAdd (x, s)) : ↥(Uq M T L)) : G) * f⁻¹ =
        ((ψ (Multiplicative.ofAdd (x, s)) : ↥(Uq M T L)) : G) := h1.symm
    calc f * ((ψ (Multiplicative.ofAdd (x, s)) : ↥(Uq M T L)) : G) =
        (f * ((ψ (Multiplicative.ofAdd (x, s)) : ↥(Uq M T L)) : G) * f⁻¹) * f := by group
      _ = _ := by rw [h2]
  have hUt' : ∀ w, ((ψ w : ↥(Uq M T L)) : G) ∈ Subgroup.centralizer (F₀ : Set G) →
      (Multiplicative.toAdd w).1 ∈ MSP.perp p := by
    intro w hw
    rw [← MSP.fixSp_xPoint hp, MSP.mem_fixSp]
    intro γ hγ
    rw [← hpF] at hγ
    obtain ⟨f, hf, rfl⟩ := hγ
    have hfc := Subgroup.mem_centralizer_iff.mp hw (f : G) (Subgroup.mem_subgroupOf.1 hf)
    have h1 := hcψ f w
    rw [commutatorElement_def, ← hfc, mul_inv_cancel_right, mul_inv_cancel, eq_comm] at h1
    have h2 := hψ1 _ h1
    have h3 : (Multiplicative.toAdd (omega5Act F (α f) w * w⁻¹)⁻¹).1 = 0 := h2
    rw [toAdd_inv, toAdd_mul, toAdd_inv, omega5Act_toAdd] at h3
    simp only [Prod.fst_neg, Prod.fst_add, neg_add_rev, neg_neg] at h3
    exact (add_neg_eq_zero.1 h3).symm
  have hfixp : ∀ y (hy : y ∈ Yq), MSP.mat (α ⟨y, hYqA hy⟩) *ᵥ p₀ = p₀ := by
    intro y hy
    have h1 := mem_fixer_of_centralizer h hAM hβ hβker hAβ hF₀A (y := ⟨y, hYqA hy⟩) (hYR hy)
    rw [hpF, MSP.commSp_xPoint hp] at h1
    exact h1 p₀ (Submodule.mem_span_singleton_self p₀)
  have hψA : ∀ x ∈ MSP.perp p, ((ψ (Multiplicative.ofAdd (x, 0)) : ↥(Uq M T L)) : G) ∈ Aq :=
    fun x hx => hAlo (hUt x hx 0)
  have hfst : ∀ (y : ↥A) (x : MSP.V4 F) (s : F),
      (Multiplicative.toAdd (omega5Act F (α y) (Multiplicative.ofAdd (x, s)) *
        (Multiplicative.ofAdd (x, s))⁻¹)⁻¹).1 = MSP.mat (α y) *ᵥ x - x := by
    intro y x s
    rw [toAdd_inv, toAdd_mul, toAdd_inv, omega5Act_toAdd, toAdd_ofAdd]
    simp only [Prod.fst_neg, Prod.fst_add]
    have : spMat (α y) *ᵥ x = MSP.mat (α y) *ᵥ x := rfl
    rw [this]
    funext i
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, neg_add_rev, neg_neg]
    rw [CharTwo.neg_eq, CharTwo.sub_eq_add, add_comm]
  have hQ : ∀ y (hy : y ∈ Yq), α ⟨y, hYqA hy⟩ ∈ MSP.qPoint p := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y₀, hy₀, hy₀Q⟩ := hcon
    set yb₀ := α ⟨y₀, hYqA hy₀⟩
    have hp₀fix : ∀ v ∈ p, MSP.mat yb₀ *ᵥ v = v := by
      intro v hv
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [Matrix.mulVec_smul, hfixp y₀ hy₀]
    obtain ⟨x₀, hx₀, hc₀⟩ : ∃ x₀ ∈ MSP.perp p, MSP.mat yb₀ *ᵥ x₀ - x₀ ∉ p := by
      by_contra hall
      push Not at hall
      exact hy₀Q (MSP.mem_qPoint.2 ⟨hp₀fix, hall⟩)
    set c₀ := MSP.mat yb₀ *ᵥ x₀ - x₀ with hc₀def
    have hc₀perp : MSP.form F p₀ c₀ = 0 := by
      have h1 : MSP.form F p₀ (MSP.mat yb₀ *ᵥ x₀) = MSP.form F p₀ x₀ := by
        rw [← MSP.form_mat yb₀ p₀ x₀, hfixp y₀ hy₀]
      rw [hc₀def, map_sub, h1, sub_self]
    have hfixc : ∀ y (hy : y ∈ Yq), MSP.mat (α ⟨y, hYqA hy⟩) *ᵥ c₀ = c₀ := by
      intro y hy
      set d₀ := (omega5Act F yb₀ (Multiplicative.ofAdd (x₀, 0)) *
        (Multiplicative.ofAdd (x₀, 0))⁻¹)⁻¹ with hd₀
      have hr₀ : ((ψ d₀ : ↥(Uq M T L)) : G) ∈ ⁅Aq, Yq⁆ := by
        rw [hd₀, ← hcψ]
        exact Subgroup.commutator_mem_commutator (hψA x₀ hx₀) hy₀
      have h1 : ⁅((ψ d₀ : ↥(Uq M T L)) : G), y⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator hr₀ hy
        rwa [hAYY, Subgroup.mem_bot] at this
      rw [hcψ ⟨y, hYqA hy⟩ d₀] at h1
      have h2 := hψ1 _ h1
      have h3 : (Multiplicative.toAdd (omega5Act F (α ⟨y, hYqA hy⟩) d₀ * d₀⁻¹)⁻¹).1 = 0 := h2
      have hd₀1 : (Multiplicative.toAdd d₀).1 = c₀ := by
        rw [hd₀]
        exact hfst ⟨y₀, hYqA hy₀⟩ x₀ 0
      rw [toAdd_inv, toAdd_mul, toAdd_inv, omega5Act_toAdd] at h3
      simp only [Prod.fst_neg, Prod.fst_add, neg_add_rev, neg_neg, hd₀1] at h3
      exact (add_neg_eq_zero.1 h3).symm
    apply hY
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    ·
      have hF2 : Fintype.card F = 2 := by rw [hcard, show k = 1 by omega, pow_one]
      have hsq : ∀ t : F, t ^ 2 = t := fun t => by
        have := FiniteField.pow_card t
        rwa [hF2] at this
      obtain ⟨x₁, hx₁p, hx₁c⟩ : ∃ x₁ : MSP.V4 F, MSP.form F p₀ x₁ = 1 ∧
          MSP.form F c₀ x₁ = MSP.form F c₀ x₀ := by
        obtain ⟨x, hx⟩ := MSP.exists_form_eq_one hp₀
        have hc₀' : c₀ ∉ MSP.perp (MSP.perp p) := by rwa [MSP.perp_perp]
        rw [MSP.mem_perp] at hc₀'
        push Not at hc₀'
        obtain ⟨z, hz, hzc⟩ := hc₀'
        have hzc' : MSP.form F c₀ z ≠ 0 := by
          rw [MSP.form_swap c₀ z] at hzc
          exact fun h0 => hzc (by rw [h0, neg_zero])
        have hpz : MSP.form F p₀ z = 0 := MSP.mem_perp_span.1 hz
        refine ⟨x + ((MSP.form F c₀ x₀ - MSP.form F c₀ x) / MSP.form F c₀ z) • z, ?_, ?_⟩
        · rw [map_add, map_smul, hx, hpz, smul_zero, add_zero]
        · rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hzc']
          ring
      rw [Subgroup.commutator_le]
      intro u hu y hy
      obtain ⟨w, hw⟩ := hψs ⟨u, hu⟩
      have hwu : ((ψ w : ↥(Uq M T L)) : G) = u := by rw [hw]
      obtain ⟨a₁, b₁, hab⟩ := Submodule.mem_span_pair.1
        (sub_mem_span_of_fix hp₀ hc₀perp (fun h' => hc₀ h') (hfixp y hy) (hfixc y hy) x₁)
      set ε := MSP.form F p₀ (Multiplicative.toAdd w).1 with hε
      set w₁ : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F) := Multiplicative.ofAdd (ε • x₁, 0)
        with hw₁
      have hw₀ : (Multiplicative.toAdd (w * w₁⁻¹)).1 ∈ MSP.perp p := by
        refine MSP.mem_perp_span.2 ?_
        rw [toAdd_mul, toAdd_inv, Prod.fst_add, Prod.fst_neg, hw₁, toAdd_ofAdd, map_add, map_neg,
          map_smul, hx₁p, smul_eq_mul, mul_one, ← hε, add_neg_cancel]
      have hsplit : ⁅u, y⁆ = ⁅((ψ (w * w₁⁻¹) : ↥(Uq M T L)) : G), y⁆ *
          ⁅((ψ w₁ : ↥(Uq M T L)) : G), y⁆ := by
        rw [← hwu, hcψ ⟨y, hYqA hy⟩, hcψ ⟨y, hYqA hy⟩, hcψ ⟨y, hYqA hy⟩, ← Subgroup.coe_mul,
          ← map_mul]
        congr 2
        have e : omega5Act F (α ⟨y, hYqA hy⟩) w =
            omega5Act F (α ⟨y, hYqA hy⟩) (w * w₁⁻¹) * omega5Act F (α ⟨y, hYqA hy⟩) w₁ := by
          rw [← omega5Act_mul, inv_mul_cancel_right]
        rw [e]
        apply Multiplicative.toAdd.injective
        simp only [toAdd_mul, toAdd_inv]
        abel
      rw [hsplit]
      refine mul_mem (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator
        (hAlo (hUt _ hw₀ (Multiplicative.toAdd (w * w₁⁻¹)).2)) hy)) ?_
      rw [hcψ ⟨y, hYqA hy⟩ w₁, hw₁, omega5Act_mul_inv_eq_two hsq hc₀perp hx₁p hx₁c hc₀def.symm
        hab.symm ε, mul_inv, map_mul, Subgroup.coe_mul]
      refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact map_omComm_le hψe hpF.ge (inv_mem (mem_omComm_xPoint_of_smul hp₀ _))
      · rw [← hcψ ⟨y₀, hYqA hy₀⟩]
        exact Subgroup.commutator_mem_commutator (hψA _ (Submodule.smul_mem _ _ hx₀)) hy₀
    ·
      have hF3 : 2 < Fintype.card F := by
        rw [hcard]
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      rw [Subgroup.commutator_le]
      intro u hu y hy
      obtain ⟨w, hw⟩ := hψs ⟨u, hu⟩
      have hwu : ((ψ w : ↥(Uq M T L)) : G) = u := by rw [hw]
      set x := (Multiplicative.toAdd w).1
      set yb := α ⟨y, hYqA hy⟩
      have hmem := sub_mem_span_of_fix hp₀ hc₀perp (fun h' => hc₀ h') (hfixp y hy) (hfixc y hy) x
      obtain ⟨a₁, b₁, hab⟩ := Submodule.mem_span_pair.1 hmem
      obtain ⟨e₂, he₂⟩ : ∃ e', e' = (omega5Act F yb₀ (Multiplicative.ofAdd (b₁ • x₀, 0)) *
          (Multiplicative.ofAdd (b₁ • x₀, 0))⁻¹)⁻¹ := ⟨_, rfl⟩
      obtain ⟨e, he⟩ : ∃ e', e' = (omega5Act F yb w * w⁻¹)⁻¹ := ⟨_, rfl⟩
      have hbx₀ : b₁ • x₀ ∈ MSP.perp p := Submodule.smul_mem _ _ hx₀
      have he₂A : ((ψ e₂ : ↥(Uq M T L)) : G) ∈ ⁅Aq, Yq⁆ := by
        rw [he₂, ← hcψ]
        exact Subgroup.commutator_mem_commutator (hψA _ hbx₀) hy₀
      have he₂1 : (Multiplicative.toAdd e₂).1 = b₁ • c₀ := by
        rw [he₂, hfst ⟨y₀, hYqA hy₀⟩ (b₁ • x₀) 0, Matrix.mulVec_smul, hc₀def, smul_sub]
      have he1 : (Multiplicative.toAdd e).1 = a₁ • p₀ + b₁ • c₀ := by
        have hw' : w = Multiplicative.ofAdd (x, (Multiplicative.toAdd w).2) := rfl
        rw [he, hw', hfst ⟨y, hYqA hy⟩ x _]
        exact hab.symm
      have he₁ : e * e₂⁻¹ ∈ omComm (MSP.xPoint p) := by
        have e3 : e * e₂⁻¹ = Multiplicative.ofAdd (a₁ • p₀,
            (Multiplicative.toAdd (e * e₂⁻¹)).2) := by
          apply Multiplicative.toAdd.injective
          rw [toAdd_ofAdd]
          refine Prod.ext ?_ rfl
          rw [toAdd_mul, toAdd_inv, Prod.fst_add, Prod.fst_neg, he1, he₂1]
          abel
        rw [e3]
        exact prod_mem_omComm_xPoint hF3 hp₀ a₁ _
      have h1 : ⁅u, y⁆ = ((ψ (e * e₂⁻¹) : ↥(Uq M T L)) : G) * ((ψ e₂ : ↥(Uq M T L)) : G) := by
        rw [← hwu, hcψ ⟨y, hYqA hy⟩ w, ← he, ← Subgroup.coe_mul, ← map_mul, inv_mul_cancel_right]
      rw [h1]
      refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right he₂A)
      exact map_omComm_le hψe hpF.ge he₁
  have hge : 2 ^ k ≤ Nat.card ↥⁅Aq, Yq⁆ := by
    obtain ⟨y₁, hy₁, hy₁X⟩ : ∃ y₁, ∃ hy₁ : y₁ ∈ Yq, α ⟨y₁, hYqA hy₁⟩ ∉ MSP.xPoint p := by
      by_contra hall
      push Not at hall
      apply hY
      refine le_sup_of_le_left ?_
      rw [Subgroup.commutator_le]
      intro u hu y hy
      have hγ := hall y hy
      rw [← hpF] at hγ
      obtain ⟨f, hf, hfy⟩ := hγ
      have hk : α (f⁻¹ * ⟨y, hYqA hy⟩) = 1 := by rw [map_mul, map_inv, hfy, inv_mul_cancel]
      have hkc := centralizer_of_eq_one h hAM hβ hβker hAβ hk
      have hku := Subgroup.mem_centralizer_iff.mp hkc u hu
      have e : ⁅u, y⁆ = ⁅u, (f : G)⁆ := by
        have hy' : y = (f : G) * ((f⁻¹ * ⟨y, hYqA hy⟩ : ↥A) : G) := by simp
        rw [hy', commutatorElement_def, commutatorElement_def]
        calc u * ((f : G) * ((f⁻¹ * ⟨y, hYqA hy⟩ : ↥A) : G)) * u⁻¹ *
              ((f : G) * ((f⁻¹ * ⟨y, hYqA hy⟩ : ↥A) : G))⁻¹
            = u * (f : G) * (((f⁻¹ * ⟨y, hYqA hy⟩ : ↥A) : G) * u⁻¹) *
                ((f⁻¹ * ⟨y, hYqA hy⟩ : ↥A) : G)⁻¹ * (f : G)⁻¹ := by group
          _ = u * (f : G) * (u⁻¹ * ((f⁻¹ * ⟨y, hYqA hy⟩ : ↥A) : G)) *
                ((f⁻¹ * ⟨y, hYqA hy⟩ : ↥A) : G)⁻¹ * (f : G)⁻¹ := by
              rw [(Subgroup.mem_centralizer_iff.mp hkc u⁻¹ (inv_mem hu))]
          _ = u * (f : G) * u⁻¹ * (f : G)⁻¹ := by group
      rw [e]
      exact Subgroup.commutator_mem_commutator hu (Subgroup.mem_subgroupOf.1 hf)
    obtain ⟨g₁, hg₁⟩ : ∃ g : MSP.Sp4 F, g = α ⟨y₁, hYqA hy₁⟩ := ⟨_, rfl⟩
    rw [← hg₁] at hy₁X
    have hg₁Q : g₁ ∈ MSP.qPoint p := hg₁ ▸ hQ y₁ hy₁
    obtain ⟨x₁, hx₁, hx₁m⟩ : ∃ x₁ ∈ MSP.perp p, MSP.mat g₁ *ᵥ x₁ ≠ x₁ := by
      by_contra hall
      push Not at hall
      exact hy₁X hall
    obtain ⟨l₁, hl₁⟩ := Submodule.mem_span_singleton.1 ((MSP.mem_qPoint.1 hg₁Q).2 x₁ hx₁)
    have hl₁0 : l₁ • p₀ ≠ 0 := by
      rw [hl₁, Ne, sub_eq_zero]
      exact hx₁m
    obtain ⟨d, hd⟩ : ∃ d : F → Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F), ∀ t, d t =
        (omega5Act F g₁ (Multiplicative.ofAdd (t • x₁, 0)) *
          (Multiplicative.ofAdd (t • x₁, 0))⁻¹)⁻¹ := ⟨_, fun _ => rfl⟩
    have hd1 : ∀ t, (Multiplicative.toAdd (d t)).1 = t • (l₁ • p₀) := by
      intro t
      rw [hd, hg₁, hfst, Matrix.mulVec_smul, ← smul_sub, ← hg₁, ← hl₁]
    have hcomm1 : ∀ t, ⁅((ψ (Multiplicative.ofAdd (t • x₁, 0)) : ↥(Uq M T L)) : G), y₁⁆ =
        ((ψ (d t) : ↥(Uq M T L)) : G) := fun t => by
      rw [hcψ ⟨y₁, hYqA hy₁⟩, hd, ← hg₁]
    let φ : F → ↥⁅Aq, Yq⁆ := fun t => ⟨((ψ (d t) : ↥(Uq M T L)) : G), by
      rw [← hcomm1]
      exact Subgroup.commutator_mem_commutator (hψA _ (Submodule.smul_mem _ t hx₁)) hy₁⟩
    have hφ : Function.Injective φ := by
      intro t t' htt
      have h0 : ((ψ (d t) : ↥(Uq M T L)) : G) = ((ψ (d t') : ↥(Uq M T L)) : G) :=
        congrArg (fun x : ↥⁅Aq, Yq⁆ => (x : G)) htt
      have h1 : ψ (d t) = ψ (d t') := Subtype.ext h0
      have h3 := hψ1 (d t * (d t')⁻¹)
        (by rw [map_mul, h1, ← map_mul, mul_inv_cancel, map_one, Subgroup.coe_one])
      have h4 : (Multiplicative.toAdd (d t * (d t')⁻¹)).1 = 0 := h3
      rw [toAdd_mul, toAdd_inv, Prod.fst_add, Prod.fst_neg, hd1, hd1, ← sub_eq_add_neg,
        ← sub_smul, smul_eq_zero] at h4
      rcases h4 with h4 | h4
      · exact sub_eq_zero.1 h4
      · exact absurd h4 hl₁0
    calc 2 ^ k = Nat.card F := by rw [Nat.card_eq_fintype_card, hcard]
      _ ≤ Nat.card ↥⁅Aq, Yq⁆ := Nat.card_le_card_of_injective φ hφ
  refine ⟨hge, fun Z' hZ'Zq hZ'c hAhi => ?_⟩
  have hArep : ∀ a ∈ Aq, ∃ w : Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F),
      (Multiplicative.toAdd w).1 ∈ MSP.perp p ∧ ∀ y ∈ Yq,
        ⁅a, y⁆ = ⁅((ψ w : ↥(Uq M T L)) : G), y⁆ := by
    intro a ha
    have hZn : Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G) ≤
        Subgroup.normalizer (Z' : Set G) := fun u hu =>
      CFSG.centralizer_le_normalizer Z' (Subgroup.mem_centralizer_iff.2 fun z hz =>
        xq_comm (hZ'Zq hz).1 (h.Uq_le_Xq hu.1))
    obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_sup_normalizer hZn (hAhi ha)
    obtain ⟨w, hw⟩ := hψs ⟨u, hu.1⟩
    have hwu : ((ψ w : ↥(Uq M T L)) : G) = u := by rw [hw]
    refine ⟨w, hUt' w (hwu ▸ hu.2), fun y hy => ?_⟩
    rw [hwu]
    have hzy : z * y = y * z := by
      have := hZ'c y (hYqA hy) z hz
      calc z * y = (y * z * y⁻¹) * y := by rw [this]
        _ = y * z := by group
    have hzu : z * u = u * z := by
      have := xq_comm (hZ'Zq hz).1 (h.Uq_le_Xq hu.1)
      exact this
    simp only [commutatorElement_def]
    calc u * z * y * (u * z)⁻¹ * y⁻¹ = u * (z * y) * z⁻¹ * u⁻¹ * y⁻¹ := by group
      _ = u * y * u⁻¹ * y⁻¹ := by rw [hzy]; group
  have hD : ∀ a ∈ Aq, ∀ y ∈ Yq, ∃ d ∈ omD p₀, ⁅a, y⁆ = ((ψ d : ↥(Uq M T L)) : G) := by
    intro a ha y hy
    obtain ⟨w, hwp, hw⟩ := hArep a ha
    refine ⟨(omega5Act F (α ⟨y, hYqA hy⟩) w * w⁻¹)⁻¹, inv_mem ?_,
      (hw y hy).trans (hcψ ⟨y, hYqA hy⟩ w)⟩
    have hw' : w = Multiplicative.ofAdd ((Multiplicative.toAdd w).1, (Multiplicative.toAdd w).2) :=
      rfl
    rw [hw']
    exact omega5Act_mul_inv_mem_omD (hQ y hy) (MSP.mem_perp_span.1 hwp) _
  have hAY_D : ⁅Aq, Yq⁆ ≤ (omD p₀).map ((Uq M T L).subtype.comp ψ) := by
    rw [Subgroup.commutator_le]
    intro a ha y hy
    obtain ⟨d, hd, he⟩ := hD a ha y hy
    exact ⟨d, hd, he.symm⟩
  have hAY_U : ⁅Aq, Yq⁆ ≤ ⁅Uq M T L, F₀⁆ ⊔ (Uq M T L ⊓ Zq M L) := by
    rintro _ hx
    obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := hAY_D hx
    have e : Multiplicative.ofAdd (c • p₀, c ^ 2 * sp4Quad F p₀) =
        Multiplicative.ofAdd (c • p₀, c ^ 2 * sp4Quad F p₀ + c) *
          Multiplicative.ofAdd ((0 : MSP.V4 F), c) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
      refine Prod.ext (by simp) ?_
      simp only [Prod.snd_add]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hrad : ((ψ (Multiplicative.ofAdd ((0 : MSP.V4 F), c)) : ↥(Uq M T L)) : G) ∈
        Uq M T L ⊓ Zq M L := by
      refine ⟨(ψ _).2, h.Uq_le_Xq (ψ _).2, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
      have h1 := hψe ⟨l, hLA hl⟩ (Multiplicative.ofAdd ((0 : MSP.V4 F), c))
      rw [omega5Act_rad _ (show (0 : MSP.V4 F) = 0 from rfl :
        Multiplicative.ofAdd ((0 : MSP.V4 F), c) ∈ omega5Rad F)] at h1
      calc l * ((ψ (Multiplicative.ofAdd ((0 : MSP.V4 F), c)) : ↥(Uq M T L)) : G)
          = (l * ((ψ (Multiplicative.ofAdd ((0 : MSP.V4 F), c)) : ↥(Uq M T L)) : G) * l⁻¹) *
              l := by group
        _ = _ := by rw [← h1]
    show (((Uq M T L).subtype.comp ψ) _ : G) ∈ _
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, e, map_mul, Subgroup.coe_mul]
    exact mul_mem (Subgroup.mem_sup_left (map_omComm_le hψe hpF.ge
      (mem_omComm_xPoint_of_smul hp₀ c))) (Subgroup.mem_sup_right hrad)
  refine ⟨le_antisymm ?_ hge, hAY_U⟩
  calc Nat.card ↥⁅Aq, Yq⁆ ≤ Nat.card ((omD p₀).map ((Uq M T L).subtype.comp ψ)) :=
        Subgroup.card_le_of_le hAY_D
    _ ≤ Nat.card (omD p₀) := Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    _ ≤ Nat.card F := card_omD_le p₀
    _ = 2 ^ k := by rw [Nat.card_eq_fintype_card, hcard]

end Core

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
theorem map_conj_stabCenter_le (hTM : T ≤ M) (g : (puAmalgam hTM).Universal)
    (δ : Vtx (puAmalgam hTM)) :
    (stabCenter (puAmalgam hTM) δ).map (MulAut.conj g).toMonoidHom ≤
      stabCenter (puAmalgam hTM) (g • δ) := by
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have hst : g * (w : (puAmalgam hTM).Universal) * g⁻¹ ∈ stab _ (g • δ) := by
    rw [mem_stab_smul]
    simp [mul_assoc]
  refine ⟨⟨_, hst⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
  have hy : g⁻¹ * (y : (puAmalgam hTM).Universal) * g ∈ stab _ δ := (mem_stab_smul _).1 y.2
  have hc : (g⁻¹ * (y : (puAmalgam hTM).Universal) * g) * w = w * (g⁻¹ * y * g) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨_, hy⟩)
  show (y : (puAmalgam hTM).Universal) * (g * w * g⁻¹) = g * w * g⁻¹ * y
  calc (y : (puAmalgam hTM).Universal) * (g * w * g⁻¹)
      = g * ((g⁻¹ * y * g) * w) * g⁻¹ := by group
    _ = g * (w * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
    _ = g * w * g⁻¹ * y := by group

omit [Finite G] in
theorem imM_le_stabCenter (hTM : T ≤ M) {K : Subgroup G}
    (hK : K ≤ M ⊓ Subgroup.centralizer (M : Set G)) :
    imM hTM K ≤ stabCenter (puAmalgam hTM) (baseA _) := by
  rintro _ ⟨k, hk, rfl⟩
  have hkM := hK (Subgroup.mem_subgroupOf.1 hk)
  have hst : (puAmalgam hTM).ofA k ∈ stab _ (baseA (puAmalgam hTM)) := by
    rw [puAmalgam.stab_baseA]
    exact ⟨k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
  refine ⟨⟨_, hst⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
  obtain ⟨m, -, hm⟩ : (y : (puAmalgam hTM).Universal) ∈ imM hTM M := by
    rw [← puAmalgam.stab_baseA]
    exact y.2
  show (y : (puAmalgam hTM).Universal) * (puAmalgam hTM).ofA k = (puAmalgam hTM).ofA k * y
  rw [← hm, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hkM.2 m m.2)

theorem d_main (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} {Y : Subgroup (puAmalgam h.le).Universal} (hS : S33Hyp h α' Y)
    (hrel : (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ k)
    (hAYY : ⁅⁅critA _ (baseA _) α', Y⁆, Y⁆ = ⊥) :
    2 ^ k ≤ Nat.card ↥⁅Y, critA _ (baseA _) α'⁆ ∧
      (Xq M = Uq M T L ⊔ Zq M L →
        Nat.card ↥⁅Y, critA _ (baseA _) α'⁆ = 2 ^ k ∧
          ⁅Y, critA _ (baseA _) α'⁆ ≤ critR _ (baseA _) α' ⊔ stabCenter _ α') := by
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hC := h.centHyp
  obtain ⟨hc, hYT, hYR, hY⟩ := hS
  obtain ⟨g, hgα, hgβ, hμ, -⟩ := exists_conj_of_isCritical _ h20 hb hc
  set μ := g⁻¹ • baseA (puAmalgam h.le) with hμdef
  have hcμ : IsCritical _ (baseA (puAmalgam h.le)) μ := ms22_iii _ h20 hb hC hμ
  have hgμ : g • μ = baseA (puAmalgam h.le) := smul_inv_smul g _
  have hconj : ∀ H K : Subgroup (puAmalgam h.le).Universal,
      (H.map (MulAut.conj g).toMonoidHom).relIndex (K.map (MulAut.conj g).toMonoidHom) =
        H.relIndex K := fun H K =>
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  have hZs' : ZM (puAmalgam h.le) α' ≤ stab _ (baseA (puAmalgam h.le)) :=
    zm_le_stab_of_isCritical _ h20 hb hc
  have hZ2' : IsPGroup 2 (ZM (puAmalgam h.le) α') := by
    have hle := (zm_le_xm _ h20 hb (hc.isMVtx_right _ h20)).trans
      (xm_le_qv_geo_one _ h20 hb hC hc)
    have hadj := adj_geo_one_of_isCritical _ hb hc
    exact (isPGroup_qv _ h20 ((isMVtx_iff_of_adj _ hadj).1 (isMVtx_baseA _))).to_le hle
  have hk2 : (2 ^ k) ^ 2 ≠ 2 ^ k := by
    have : 2 ≤ 2 ^ k := Nat.le_self_pow (by have := hd.1; omega) 2
    intro h'
    nlinarith
  obtain ⟨p', hp', hp'Z⟩ : ∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧
      S5.vIm h.le a (ZM _ α') = MSP.xPoint p := by
    rcases shape_of_sp4Data h hd hc with ⟨-, -, hpZ⟩ | ⟨h1, -, -⟩
    · exact hpZ
    · rw [hrel] at h1
      exact absurd (le_antisymm (Nat.le_self_pow (by norm_num) _) h1).symm hk2
  have hrelμ : (Qv _ μ).relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ k := by
    have e1 : (Qv _ μ).relIndex (ZM (puAmalgam h.le) (baseA _)) =
        (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') := by
      rw [← hconj (Qv _ μ) (ZM _ (baseA _)), ← qv_smul, ← zm_smul, hgμ, hgα]
    rw [e1, relIndex_qv_baseA_eq_card h hd hZs' hZ2', hp'Z, MSP.card_xPoint hp',
      Nat.card_eq_fintype_card, hd.2.1]
  obtain ⟨p, hp, hpZ⟩ : ∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧
      S5.vIm h.le a (ZM _ μ) = MSP.xPoint p := by
    rcases shape_of_sp4Data h hd hcμ with ⟨-, -, hpZ⟩ | ⟨h1, -, -⟩
    · exact hpZ
    · rw [hrelμ] at h1
      exact absurd (le_antisymm (Nat.le_self_pow (by norm_num) _) h1).symm hk2
  obtain ⟨p₀, hp₀, rfl⟩ := MSP.exists_eq_span_of_isPoint hp
  set Y' := Y.map (MulAut.conj g⁻¹).toMonoidHom with hY'
  have hYY : Y = Y'.map (MulAut.conj g).toMonoidHom := (map_conj_map_conj_inv Y g).symm
  set A' := XM (puAmalgam h.le) (baseA _) ⊓ Qv _ μ with hA'
  have hAA : critA (puAmalgam h.le) (baseA _) α' = A'.map (MulAut.conj g).toMonoidHom := by
    rw [critA, hA', Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← xm_smul, ← qv_smul, hgα,
      hgμ]
  have hRR : critR (puAmalgam h.le) (baseA _) α' =
      (⁅ZM (puAmalgam h.le) μ, ZM _ (baseA _)⁆).map (MulAut.conj g).toMonoidHom := by
    rw [critR, Subgroup.map_commutator, ← zm_smul, ← zm_smul, hgμ, hgα, Subgroup.commutator_comm]
  have hY'T : Y' ≤ imM h.le T := by
    rw [← puAmalgam.qv_baseB, ← map_conj_le_map_conj_iff g, ← hYY, ← qv_smul, hgβ]
    exact hYT
  have hY'R : Y' ≤ Subgroup.centralizer
      ((⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (baseA _)⁆ :
        Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) := by
    rw [← map_conj_le_map_conj_iff g, ← hYY, ← PU.centralizer_map_mulEquiv, ← hRR]
    exact hYR
  have hY'M : Y' ≤ imM h.le M := hY'T.trans (imM_mono h.le h.le)
  have hXim : imM h.le (Xq M) = XM (puAmalgam h.le) (baseA _) := by
    rw [puAmalgam.xm_baseA, h.normalCoreIn_eq]
  have hA'M : A' ≤ imM h.le M := by
    refine inf_le_left.trans ?_
    rw [← hXim]
    exact imM_mono h.le (Xq_le M)
  have hZμs : ZM (puAmalgam h.le) μ ≤ stab _ (baseA (puAmalgam h.le)) :=
    zm_le_stab_of_isCritical _ h20 hb hcμ
  have hZμM : ZM (puAmalgam h.le) μ ≤ imM h.le M := by rwa [← puAmalgam.stab_baseA]
  have hZμX : ZM (puAmalgam h.le) μ ≤ XM _ μ := zm_le_xm _ h20 hb (hcμ.isMVtx_right _ h20)
  set F₀ := pre h.le (ZM (puAmalgam h.le) μ) with hF₀
  set Yq := pre h.le Y' with hYq
  set Aq := pre h.le A' with hAq
  have hF₀im : imM h.le F₀ = ZM _ μ := imM_pre h.le hZμM
  have hYqim : imM h.le Yq = Y' := imM_pre h.le hY'M
  have hAqim : imM h.le Aq = A' := imM_pre h.le hA'M
  have hF₀M : F₀ ≤ M := pre_le h.le _
  have hYqM : Yq ≤ M := pre_le h.le _
  have hAqM : Aq ≤ M := pre_le h.le _
  have hZ0im : imM h.le (Z0q M T) = ZM (puAmalgam h.le) (baseA _) := (puAmalgam.zm_baseA h.le).symm
  have hpF : (F₀.subgroupOf M).map a = MSP.xPoint (F ∙ p₀) := by
    rw [← vIm_eq_map_pre h a]
    exact hpZ
  have hQZ : Qv (puAmalgam h.le) μ ≤ Subgroup.centralizer (ZM (puAmalgam h.le) μ : Set _) :=
    (qv_le_centralizer_xm _ μ).trans (Subgroup.centralizer_le hZμX)
  have hpreQ : pre h.le (Qv _ μ) ≤ Subgroup.centralizer (F₀ : Set G) :=
    pre_le_centralizer h.le hF₀M (by rw [hF₀im]; exact hQZ)
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hUF₀ : ⁅Uq M T L, F₀⁆ ≤ Uq M T L := commutator_le_left_of_le_normalizer (hF₀M.trans hUn)
  have hUZ : imM h.le (Uq M T L) ≤ ZM (puAmalgam h.le) (baseA _) := by
    rw [← hZ0im]
    exact imM_mono h.le (Uq_le_Z0q h.L_le)
  have himUF : imM h.le ⁅Uq M T L, F₀⁆ ≤
      ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (baseA _)⁆ := by
    rw [imM_commutator h.le (Uq_le h.L_le) hF₀M, hF₀im, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hUZ
  have hYR' : Yq ≤ Subgroup.centralizer ((⁅Uq M T L, F₀⁆ : Subgroup G) : Set G) :=
    pre_le_centralizer h.le (hUF₀.trans (Uq_le h.L_le))
      (hY'R.trans (Subgroup.centralizer_le himUF))
  have hnat := hd.2.2.2
  rw [← h.Uq_inf_Zq] at hnat
  obtain ⟨c⟩ := MSP.nonempty_natCoord hnat
  have hK12 : Uq M T L ⊓ pre h.le (Qv _ μ) ≤ Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G) :=
    inf_le_inf_left _ hpreQ
  have hK1 : (Uq M T L ⊓ pre h.le (Qv _ μ)).relIndex (Uq M T L) ≤ 2 ^ k := by
    rw [inf_comm, Subgroup.inf_relIndex_right, relIndex_pre h.le _ (Uq_le h.L_le), ← hrelμ]
    exact Subgroup.relIndex_le_of_le_right hUZ (by rw [hrelμ]; positivity)
  have hK2 : 2 ^ k ≤ (Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G)).relIndex (Uq M T L) := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    have h1 := card_le_fixSp_mul h le_rfl c F₀
    have hpt : MSP.IsPoint (F ∙ p₀) := MSP.isPoint_span hp₀
    rw [hpF, MSP.card_V4, MSP.card_fixSp, MSP.fixSp_xPoint hpt] at h1
    have h3 : Module.finrank F (MSP.perp (F ∙ p₀)) = 3 := by
      have := MSP.finrank_perp (F ∙ p₀)
      rw [hpt] at this
      omega
    rw [h3, Nat.card_eq_fintype_card, hd.2.1] at h1
    have hq : 0 < (2 ^ k) ^ 3 := by positivity
    have : (2 ^ k) ^ 3 * 2 ^ k ≤ (2 ^ k) ^ 3 *
        (Subgroup.centralizer (F₀ : Set G)).relIndex (Uq M T L) := by
      rw [← pow_succ]
      exact h1
    exact Nat.le_of_mul_le_mul_left this hq
  have hK21 : Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G) ≤ Uq M T L ⊓ pre h.le (Qv _ μ) := by
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hK12 inf_le_left
    have hpos : 0 < (Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G)).relIndex (Uq M T L) :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h1 : (Uq M T L ⊓ pre h.le (Qv _ μ)).relIndex
        (Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G)) = 1 := by
      have h0 : (Uq M T L ⊓ pre h.le (Qv _ μ)).relIndex
          (Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G)) ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      have : (Uq M T L ⊓ pre h.le (Qv _ μ)).relIndex
          (Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G)) *
            (Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G)).relIndex (Uq M T L) ≤
          1 * (Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G)).relIndex (Uq M T L) := by
        rw [hmul, one_mul]
        exact hK1.trans hK2
      have := Nat.le_of_mul_le_mul_right this hpos
      omega
    exact Subgroup.relIndex_eq_one.1 h1
  have hAlo : Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G) ≤ Aq := by
    intro u hu
    have huM : u ∈ M := Uq_le h.L_le hu.1
    have huQ := (hK21 hu).2
    refine (mem_pre_iff h.le ⟨u, huM⟩).2 ⟨?_, ?_⟩
    · rw [← hXim]
      exact (ofA_mem_imM_iff h.le _).2 (h.Uq_le_Xq hu.1)
    · exact (mem_pre_iff h.le ⟨u, huM⟩).1 huQ
  have hMM : ⁅M, M⁆ ≤ M := commutator_le_left_of_le_normalizer Subgroup.le_normalizer
  have hAYqM : ⁅Aq, Yq⁆ ≤ M := (Subgroup.commutator_mono hAqM hYqM).trans hMM
  have himAY : imM h.le ⁅Aq, Yq⁆ = ⁅A', Y'⁆ := by
    rw [imM_commutator h.le hAqM hYqM, hAqim, hYqim]
  have hAYY' : ⁅⁅Aq, Yq⁆, Yq⁆ = ⊥ := by
    have hM3 : ⁅⁅Aq, Yq⁆, Yq⁆ ≤ M := (Subgroup.commutator_mono hAYqM hYqM).trans hMM
    rw [← imM_eq_bot_iff h.le hM3, imM_commutator h.le hAYqM hYqM, himAY, hYqim]
    rw [hAA, hYY, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at hAYY
    exact hAYY
  have hYqT : Yq ≤ T := pre_le_of_le_imM h hY'T
  have hZY : ⁅ZM (puAmalgam h.le) (baseA _), Y'⁆ = imM h.le ⁅Uq M T L, Yq⁆ := by
    rw [← commutator_Z0q_eq h hYqT, imM_commutator h.le (Z0q_le M T) hYqM, hZ0im, hYqim]
  have hY' : ¬ ⁅Uq M T L, Yq⁆ ≤ ⁅Uq M T L, F₀⁆ ⊔ ⁅Aq, Yq⁆ := by
    intro hle
    apply hY
    have hUF₀M : ⁅Uq M T L, F₀⁆ ≤ M := hUF₀.trans (Uq_le h.L_le)
    have h1 : ⁅ZM (puAmalgam h.le) (baseA _), Y'⁆ ≤
        ⁅XM (puAmalgam h.le) (baseA _), XM _ μ⁆ ⊔ ⁅A', Y'⁆ := by
      rw [hZY]
      refine (imM_mono h.le hle).trans ?_
      rw [imM_sup h.le hUF₀M hAYqM, himAY, imM_commutator h.le (Uq_le h.L_le) hF₀M, hF₀im]
      refine sup_le_sup_right (Subgroup.commutator_mono ?_ hZμX) _
      rw [← hXim]
      exact imM_mono h.le h.Uq_le_Xq
    have hL : ⁅ZM (puAmalgam h.le) α', Y⁆ =
        (⁅ZM (puAmalgam h.le) (baseA _), Y'⁆).map (MulAut.conj g).toMonoidHom := by
      rw [hYY, ← hgα, zm_smul, Subgroup.map_commutator]
    have hR : ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
        ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆ =
        (⁅XM (puAmalgam h.le) (baseA _), XM _ μ⁆ ⊔ ⁅A', Y'⁆).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_commutator, ← xm_smul, ← xm_smul,
        hgμ, hgα, ← hAA, ← hYY, Subgroup.commutator_comm (XM _ α')]
    rw [hL, hR]
    exact Subgroup.map_mono h1
  have hCM := (sp4Lift_holds G M T L h k F _ _ a hd).2.1
  have hCfix : ∀ m ∈ M, ∀ z ∈ Uq M T L ⊓ Zq M L, m * z * m⁻¹ = z := by
    intro m hm z hz
    rw [h.Uq_inf_Zq, hCM] at hz
    rw [Subgroup.mem_centralizer_iff.mp hz.2 m hm, mul_inv_cancel_right]
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := id hnat
  have hAβ := isCoordAct_of_natSp hβα
  obtain ⟨hge, hcore⟩ := d_core h le_rfl hβ hβker hAβ hd.1 hd.2.1 h.L_le hd.2.2.1 hCfix hF₀M hYqM
    hp₀ hpF hAlo hYR' hAYY' hY'
  have hYA : ⁅Y, critA (puAmalgam h.le) (baseA _) α'⁆ =
      (imM h.le ⁅Aq, Yq⁆).map (MulAut.conj g).toMonoidHom := by
    rw [himAY, hYY, hAA, ← Subgroup.map_commutator, Subgroup.commutator_comm]
  have hcardYA : Nat.card ↥⁅Y, critA (puAmalgam h.le) (baseA _) α'⁆ = Nat.card ↥⁅Aq, Yq⁆ := by
    rw [hYA, Subgroup.card_map_of_injective (MulAut.conj g).injective, card_imM h.le hAYqM]
  refine ⟨hcardYA ▸ hge, fun hXU => ?_⟩
  have hAhi : Aq ≤ (Uq M T L ⊓ Subgroup.centralizer (F₀ : Set G)) ⊔
      (Zq M L ⊓ Subgroup.centralizer (M : Set G)) := by
    intro x hx
    have hxM := hAqM hx
    have hx' := (mem_pre_iff h.le ⟨x, hxM⟩).1 hx
    have hxX : x ∈ Xq M := by
      have := hx'.1
      rw [← hXim] at this
      exact (ofA_mem_imM_iff h.le _).1 this
    have hxC : x ∈ Subgroup.centralizer (F₀ : Set G) :=
      hpreQ ((mem_pre_iff h.le ⟨x, hxM⟩).2 hx'.2)
    have hxUC : x ∈ Uq M T L ⊔ (Zq M L ⊓ Subgroup.centralizer (M : Set G)) := by
      rcases Nat.lt_or_ge k 2 with hk | hk
      ·
        obtain rfl : k = 1 := by have := hd.1; omega
        have htr : MSP.transv p₀ 1 ∈ (F₀.subgroupOf M).map a := by
          rw [hpF]
          exact MSP.transv_mem_xPoint p₀ 1
        obtain ⟨z, hz, hza⟩ := htr
        have hodd : a z ∉ commutator (MSP.Sp4 F) := by
          rw [hza]
          exact MSP.transv_not_mem_commutator_of_card_two
            (by rw [Nat.card_eq_fintype_card, hd.2.1, pow_one]) hp₀ 1 one_ne_zero
        refine S5Q2.xq_inf_centralizer_le h hd hXU hodd ⟨hxX, ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hxC _ (Subgroup.mem_subgroupOf.1 hz)).symm
      · have hZc := S5Q2.zq_le_centralizer_of_two_le h hd hk
        rw [hXU] at hxX
        exact (sup_le_sup_left (le_inf le_rfl hZc) _) hxX
    have hZn : Uq M T L ≤ Subgroup.normalizer
        ((Zq M L ⊓ Subgroup.centralizer (M : Set G) : Subgroup G) : Set G) := fun u hu =>
      CFSG.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun z hz =>
        (Subgroup.mem_centralizer_iff.1 hz.2 u (Uq_le h.L_le hu)).symm)
    obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_sup_normalizer hZn hxUC
    have hzC : z ∈ Subgroup.centralizer (F₀ : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun f hf => (Subgroup.mem_centralizer_iff.mp hz.2 f (hF₀M hf))
    have huC : u ∈ Subgroup.centralizer (F₀ : Set G) := by
      have : u = (u * z) * z⁻¹ := by group
      rw [this]
      exact mul_mem hxC (inv_mem hzC)
    exact mul_mem (Subgroup.mem_sup_left ⟨hu, huC⟩) (Subgroup.mem_sup_right hz)
  obtain ⟨hcard, hle⟩ := hcore _ inf_le_left (fun m hm z hz => by
    rw [(Subgroup.mem_centralizer_iff.mp hz.2 m hm), mul_inv_cancel_right]) hAhi
  refine ⟨hcardYA.trans hcard, ?_⟩
  have hUF₀M : ⁅Uq M T L, F₀⁆ ≤ M := hUF₀.trans (Uq_le h.L_le)
  have hUCM : Uq M T L ⊓ Zq M L ≤ M := inf_le_left.trans (Uq_le h.L_le)
  have h1 : imM h.le ⁅Aq, Yq⁆ ≤ ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (baseA _)⁆ ⊔
      stabCenter _ (baseA (puAmalgam h.le)) := by
    refine (imM_mono h.le hle).trans ?_
    rw [imM_sup h.le hUF₀M hUCM]
    have hUZc : Uq M T L ⊓ Zq M L ≤ Subgroup.centralizer (M : Set G) := by
      rw [h.Uq_inf_Zq, hCM]
      exact inf_le_right
    refine sup_le_sup ?_ (imM_le_stabCenter h.le (le_inf hUCM hUZc))
    rw [imM_commutator h.le (Uq_le h.L_le) hF₀M, hF₀im, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hUZ
  have hcen : (stabCenter (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom ≤
      stabCenter _ α' := by
    have := map_conj_stabCenter_le h.le g (baseA (puAmalgam h.le))
    rwa [hgα] at this
  rw [hYA, hRR]
  refine (Subgroup.map_mono h1).trans ?_
  rw [Subgroup.map_sup]
  exact sup_le_sup le_rfl hcen

theorem s33D5_holds :
    ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
      (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a → ⁅Xq M, L⁆ ≤ Uq M T L →
      ∀ (α' : Vtx (puAmalgam h.le)) (Y : Subgroup (puAmalgam h.le).Universal), S33Hyp h α' Y →
        Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal) →
        (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ k →
        Xq M = Uq M T L ⊔ Zq M L →
        ⁅⁅critA _ (baseA _) α', Y⁆, Y⁆ = ⊥ →
          Nat.card ↥⁅Y, critA _ (baseA _) α'⁆ = 2 ^ k ∧
            ⁅Y, critA _ (baseA _) α'⁆ ≤ critR _ (baseA _) α' ⊔ stabCenter _ α' := by
  intro G _ _ M T L h k F _ _ a hd _ α' Y hS _ hrel hXU hAYY
  exact (d_main h hd hS hrel hAYY).2 hXU

end Main

end CFSG.Quasithin.MS93.S33
