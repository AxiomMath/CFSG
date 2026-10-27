module

public import CFSG.RankThree.GF2n.Smith81.S81TBridge
public import CFSG.RankThree.GF2n.Smith81.S81TModelE5
public import CFSG.RankThree.GF2n.Smith81.S81TModelE4
public import CFSG.RankThree.GF2n.Smith81.S81E5Tr
public import CFSG.RankThree.GF2n.Smith81.S81D6Model
public import CFSG.RankThree.GF2n.Smith81.ESetup

public section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.EGeom CFSG.RankThree.GF2n.Smith81.E3LCond
open scoped commutatorElement

section Transport

variable {G : Type} [Group G] {M Q Z B : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {E' : Type} [AddCommGroup E'] [Module K E']
  {ψ : M₀.E ≃ₗ[K] E'} {φ : Lgen M (LB M Q B) →* (E' ≃ₗ[K] E')} {Γ : Subgroup (E' ≃ₗ[K] E')}
  {p₀ : E'} {U₀ : Subgroup (E' ≃ₗ[K] E')}

theorem eUniData_transport (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {c : E' ≃ₗ[K] E'} (hcΓ : c ∈ Γ) :
    EUniData M Q Z B M₀ (ψ.trans c) ((MulAut.conj c).toMonoidHom.comp φ) Γ p₀ U₀ := by
  refine ⟨?_, ?_, d.le_normalizer, ?_, ?_⟩
  · rw [MonoidHom.range_comp, d.range]
    ext v
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact mul_mem (mul_mem hcΓ ha) (inv_mem hcΓ)
    · intro hv
      exact ⟨c⁻¹ * v * c, mul_mem (mul_mem (inv_mem hcΓ) hv) hcΓ, by group⟩
  · intro s
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← d.ker s]
    constructor
    · intro h
      have h1 : c * φ s = c := mul_inv_eq_one.mp h
      exact mul_left_cancel (h1.trans (mul_one c).symm)
    · intro h
      rw [h]
      group
  · intro s x hx
    have h := d.equivariant s x hx
    simp only [LinearEquiv.trans_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.coe_coe]
    rw [h]
    simp
  · intro A hA hAQ hAZ
    obtain ⟨g₀, hg₀, himg, hU⟩ := d.point A hA hAQ hAZ
    refine ⟨c * g₀, mul_mem hcΓ hg₀, ?_, ?_⟩
    · ext v
      simp only [Set.mem_image, SetLike.mem_coe, LinearEquiv.trans_apply]
      constructor
      · rintro ⟨a, haA, rfl⟩
        have : ψ (M₀.π a) ∈ (fun a : G => ψ (M₀.π a)) '' (A : Set G) := ⟨a, haA, rfl⟩
        rw [himg] at this
        obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp this
        refine Submodule.mem_span_singleton.mpr ⟨s, ?_⟩
        rw [← hs]
        simp
      · intro hv
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
        have : s • g₀ p₀ ∈ (fun a : G => ψ (M₀.π a)) '' (A : Set G) := by
          rw [himg]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        obtain ⟨a, haA, ha⟩ := this
        refine ⟨a, haA, ?_⟩
        rw [show ψ (M₀.π a) = s • g₀ p₀ from ha]
        simp
    · intro u hu
      obtain ⟨u₀, hu₀, rfl⟩ := EGeom.mem_conjSub.mp hu
      obtain ⟨s, hsQ, hsφ⟩ := hU (g₀ * u₀ * g₀⁻¹) (EGeom.mem_conjSub.mpr ⟨u₀, hu₀, rfl⟩)
      refine ⟨s, hsQ, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hsφ]
      group

end Transport

section Core

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {E' : Type} [AddCommGroup E'] [Module K E'] {ψ : M₀.E ≃ₗ[K] E'}
  {φ : Lgen M (LB M Q B) →* (E' ≃ₗ[K] E')} {Γ : Subgroup (E' ≃ₗ[K] E')} {p₀ : E'}
  {U₀ : Subgroup (E' ≃ₗ[K] E')} {X : Subgroup G} {x : G}

theorem exists_x0_of_normQuot (hs : Sit M Q Z X x)
    (hN : Nat.card ↥X ≤ 2 * Nat.card ↥(X ⊓ Lgen M (LB M Q B))) :
    ∃ (x₀ : G) (_ : x₀ ∈ Lgen M (LB M Q B)), Sit M Q Z X x₀ ∧ IsConj x x₀ := by
  have H : StrothHyp M Q Z := hs.hyp
  have h12 := smith_1_12 hs
  have hcardX : Nat.card X = Nat.card Z := IsZConjugate.card_eq hs.conj
  have hcard4 : 4 ≤ Nat.card X := hcardX ▸ H.q4
  have hone : 1 < Nat.card ↥(X ⊓ Lgen M (LB M Q B)) := by omega
  obtain ⟨x₀, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp hone)
  obtain ⟨hx₀X, hx₀L⟩ := Subgroup.mem_inf.mp x₀.2
  have hx₀1' : (x₀ : G) ≠ 1 := fun h => hx₀1 (Subtype.ext (h.trans (Subgroup.coe_one _).symm))
  have hx₀M : (x₀ : G) ∈ M := (Subgroup.mem_inf.mp (h12.1 hx₀X)).1
  have hx₀Q : (x₀ : G) ∉ Q := fun h => by
    have : (x₀ : G) ∈ X ⊓ Q := ⟨hx₀X, h⟩
    rw [h12.2, Subgroup.mem_bot] at this
    exact hx₀1' this
  have hs₀ : Sit M Q Z X (x₀ : G) := ⟨H, hs.conj, hx₀X, hx₀1', hx₀M, hx₀Q⟩
  refine ⟨x₀, hx₀L, hs₀, ?_⟩
  obtain ⟨g₁, hg₁⟩ := hs.conj
  have hxZ : g₁⁻¹ * x * g₁ ∈ Z := mem_conjSubgroup.mp (hg₁ ▸ hs.mem)
  have hx₀Z : g₁⁻¹ * (x₀ : G) * g₁ ∈ Z := mem_conjSubgroup.mp (hg₁ ▸ hx₀X)
  have hz1 : g₁⁻¹ * x * g₁ ≠ 1 := fun h => hs.ne_one (by
    have := congrArg (fun y => g₁ * y * g₁⁻¹) h
    simpa [mul_assoc] using this)
  have hz₀1 : g₁⁻¹ * (x₀ : G) * g₁ ≠ 1 := fun h => hx₀1' (by
    have := congrArg (fun y => g₁ * y * g₁⁻¹) h
    simpa [mul_assoc] using this)
  obtain ⟨m, -, hm⟩ := Z_isConj H hxZ hz1 hx₀Z hz₀1
  refine isConj_iff.mpr ⟨g₁ * m * g₁⁻¹, ?_⟩
  have e1 : (x₀ : G) = g₁ * (m * (g₁⁻¹ * x * g₁) * m⁻¹) * g₁⁻¹ := by
    rw [hm]
    group
  rw [e1]
  group

theorem e28_core {β' : E' → E' → K} (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀)
    (hForm : ∀ (ψ' : M₀.E ≃ₗ[K] E') (φ' : Lgen M (LB M Q B) →* (E' ≃ₗ[K] E')),
      EUniData M Q Z B M₀ ψ' φ' Γ p₀ U₀ →
        ∃ lam : K, lam ≠ 0 ∧ ∀ e f : M₀.E, M₀.B e f = lam * β' (ψ' e) (ψ' f))
    (hcl : ∀ t ∈ Γ, t * t = 1 → t ≠ 1 → ∃ g ∈ Γ,
      InvolK12 Γ p₀ β' (g * t * g⁻¹) ∨ InvolK3 Γ β' (g * t * g⁻¹))
    {x₀ : G} (hx₀L : x₀ ∈ Lgen M (LB M Q B)) (hs₀ : Sit M Q Z X x₀) (hQX : Q ⊓ QB X ≠ ⊥) :
    ∃ v : G, IsConj x₀ v ∧ v ∈ Q ∧ v ∈ QB X := by
  have hΓ : φ ⟨x₀, hx₀L⟩ ∈ Γ := by
    rw [← d.range]
    exact ⟨_, rfl⟩
  have h2 : φ ⟨x₀, hx₀L⟩ * φ ⟨x₀, hx₀L⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x₀, hx₀L⟩ : Lgen M (LB M Q B)) * ⟨x₀, hx₀L⟩ = 1 := Subtype.ext hs₀.x_sq
    rw [this, map_one]
  have h1 : φ ⟨x₀, hx₀L⟩ ≠ 1 := fun h => hs₀.notQ ((d.ker ⟨x₀, hx₀L⟩).mp h)
  obtain ⟨g, hg, hM⟩ := hcl _ hΓ h2 h1
  have d' := eUniData_transport d hg
  obtain ⟨lam, hlam, hB⟩ := hForm _ _ d'
  have hφ' : ((MulAut.conj g).toMonoidHom.comp φ) ⟨x₀, hx₀L⟩ = g * φ ⟨x₀, hx₀L⟩ * g⁻¹ := rfl
  rcases hM with hM12 | hM3
  · exact e28_of_involK12 hc hD d' hB hs₀ hx₀L hφ' hM12 hQX
  · exact e28_of_involK3 hD d' hlam hB hs₀ hx₀L hφ' hM3 hQX

end Core

end CFSG.RankThree.GF2n.Smith81.MinuscT

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.MinuscT
open scoped commutatorElement


@[expose] def E5_28CondStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE5 M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      Q ⊓ QB X ≠ ⊥ → ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

@[expose] def E4_28CondStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE4 M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      Q ⊓ QB X ≠ ⊥ → ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

@[expose] def E5InvolClassesStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ t ∈ EAut K, t * t = 1 → t ≠ 1 →
      ∃ g ∈ EAut K, ∃ S ∈ e5Reps, ∀ v : V K, (g * t * g⁻¹) v = tOp K S v

@[expose] def E4InvolClassesStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ t ∈ EAut0 K, t * t = 1 → t ≠ 1 →
      ∃ g ∈ EAut0 K, ∃ S ∈ e4Reps, ∀ w : W K, emb K ((g * t * g⁻¹) w) = tOp K S (emb K w)

@[expose] def NormQuotE5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE5 M Q Z B → ∀ E : Subgroup G, E ≤ H0 M Z → IsPGroup 2 E →
      Nat.card ↥E ≤ 2 * Nat.card ↥(E ⊓ Lgen M (LB M Q B))

@[expose] def NormQuotE4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE4 M Q Z B → ∀ E : Subgroup G, E ≤ H0 M Z → IsPGroup 2 E →
      Nat.card ↥E ≤ 2 * Nat.card ↥(E ⊓ Lgen M (LB M Q B))

section Cond


theorem e528Cond_of_uniform
    (hFE1 : Smith24E5UniformStatement) (hForm : Smith24E5FormStatement)
    (hN : NormQuotE5Statement) (hCl : E5InvolClassesStatement) : E5_28CondStatement := by
  intro G _ _ M Q Z B IH hc h5 X x hs hQX
  have H : StrothHyp M Q Z := hc.ctx.hyp
  have h12 := smith_1_12 hs
  obtain ⟨K, _, _, hK2, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h5 K γ M₀ hD
  have hXle : X ≤ H0 M Z := h12.1
  have hX2 : IsPGroup 2 X := fun y => ⟨1, Subtype.ext (by
    have := hs.X_sq y y.2
    simpa [pow_two] using this)⟩
  have hNQ := hN G M Q Z B IH hc h5 X hXle hX2
  obtain ⟨x₀, hx₀L, hs₀, hxx₀⟩ := exists_x0_of_normQuot hs hNQ
  have hq4 : 4 ≤ Nat.card K := hD.card ▸ H.q4
  have hcl : ∀ t ∈ EAut K, t * t = 1 → t ≠ 1 → ∃ g ∈ EAut K,
      InvolK12 (EAut K) (w0 : V K) beta (g * t * g⁻¹) ∨ InvolK3 (EAut K) beta (g * t * g⁻¹) := by
    intro t ht ht2 ht1
    obtain ⟨g, hg, S, hS, hgt⟩ := hCl K hq4 t ht ht2 ht1
    exact ⟨g, hg, involModel_E5 hq4 hS hgt⟩
  obtain ⟨v, hv, hvQ, hvX⟩ := e28_core hc.ctx hD d
    (hForm G M Q Z B IH hc.toRemCfg h5 K γ M₀ hD) hcl hx₀L hs₀ hQX
  exact ⟨v, hxx₀.trans hv, hvQ, hvX⟩

theorem e428Cond_of_uniform
    (hFE1 : Smith24E4UniformStatement) (hForm : Smith24E4FormStatement)
    (hN : NormQuotE4Statement) (hCl : E4InvolClassesStatement) : E4_28CondStatement := by
  intro G _ _ M Q Z B IH hc h4 X x hs hQX
  have H : StrothHyp M Q Z := hc.ctx.hyp
  have h12 := smith_1_12 hs
  obtain ⟨K, _, _, hK2, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h4 K γ M₀ hD
  have hXle : X ≤ H0 M Z := h12.1
  have hX2 : IsPGroup 2 X := fun y => ⟨1, Subtype.ext (by
    have := hs.X_sq y y.2
    simpa [pow_two] using this)⟩
  have hNQ := hN G M Q Z B IH hc h4 X hXle hX2
  obtain ⟨x₀, hx₀L, hs₀, hxx₀⟩ := exists_x0_of_normQuot hs hNQ
  have hq4 : 4 ≤ Nat.card K := hD.card ▸ H.q4
  have hcl : ∀ t ∈ EAut0 K, t * t = 1 → t ≠ 1 → ∃ g ∈ EAut0 K,
      InvolK12 (EAut0 K) (p0 K) betaW (g * t * g⁻¹) ∨ InvolK3 (EAut0 K) betaW (g * t * g⁻¹) := by
    intro t ht ht2 ht1
    obtain ⟨g, hg, S, hS, hgt⟩ := hCl K hq4 t ht ht2 ht1
    exact ⟨g, hg, involModel_E4 hq4 hS hgt⟩
  obtain ⟨v, hv, hvQ, hvX⟩ := e28_core hc.ctx hD d
    (hForm G M Q Z B IH hc.toRemCfg h4 K γ M₀ hD) hcl hx₀L hs₀ hQX
  exact ⟨v, hxx₀.trans hv, hvQ, hvX⟩

end Cond

end CFSG.RankThree.GF2n.Smith81
