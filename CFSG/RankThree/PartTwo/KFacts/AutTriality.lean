module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsSep
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {f : ℕ} {K : Type} [Field K] [Finite K]

variable (σ : K ≃+* K)

@[expose] noncomputable def stdPinnedTriality :
    PinnedAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) where
  inndiag := (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
    MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range
  inn_le := le_rfl
  field := (fieldActorHom (t := TwistTag.D4) σ).range
  graph := ∅

@[expose] def trialityHasKind (τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    AutKind → Prop
  | .inner => IsInnerAut τ
  | .diagonal => False
  | .field => ∃ δ : K ≃+* K, δ ≠ 1 ∧ Nat.Coprime (orderOf δ) 3 ∧
      ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        τ = MulAut.conj g * fieldActor σ δ * (MulAut.conj g)⁻¹
  | .graph => False
  | .graphField => ∃ δ : K ≃+* K, 3 ∣ orderOf δ ∧ IsInnerAut (τ * (fieldActor σ δ)⁻¹)

variable {σ}

section NormalForm

variable (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
include hf hK hσ

theorem exists_conj_mul_fieldActor (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      α = MulAut.conj g * fieldActor σ δ := by
  obtain ⟨-, hex, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hex α
  exact ⟨g, δ, hgδ⟩

theorem isInnerAut_fieldActor_iff {δ : K ≃+* K} :
    IsInnerAut (fieldActor (t := TwistTag.D4) σ δ) ↔ δ = 1 := by
  obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  constructor
  · intro hin
    have h1 : Θ (fieldActor σ δ) = δ := hΘ _ 1 δ (by rw [map_one, one_mul])
    have h2 : fieldActor (t := TwistTag.D4) σ δ ∈ Θ.ker := by rw [hker]; exact hin
    rw [MonoidHom.mem_ker, h1] at h2
    exact h2
  · rintro rfl
    rw [fieldActor_one]
    exact ⟨1, map_one _⟩

omit hf hK hσ in
theorem fieldActor_mul_comm (δ ε : K ≃+* K) :
    fieldActor (t := TwistTag.D4) σ δ * fieldActor σ ε =
      fieldActor σ ε * fieldActor (t := TwistTag.D4) σ δ := by
  rw [← fieldActor_mul, ← fieldActor_mul,
    CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K δ ε]

theorem exists_conj_eq_conj_fieldActor
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ δ : K ≃+* K,
      α * fieldActor σ δ * α⁻¹ = MulAut.conj g * fieldActor σ δ * (MulAut.conj g)⁻¹ := by
  obtain ⟨g, ε, rfl⟩ := exists_conj_mul_fieldActor hf hK hσ α
  refine ⟨g, fun δ => ?_⟩
  have h1 := fieldActor_mul_comm (σ := σ) ε δ
  calc MulAut.conj g * fieldActor σ ε * fieldActor σ δ * (MulAut.conj g * fieldActor σ ε)⁻¹ =
      MulAut.conj g * (fieldActor σ ε * fieldActor σ δ) * (fieldActor σ ε)⁻¹ *
        (MulAut.conj g)⁻¹ := by group
    _ = _ := by rw [h1]; group

omit hf hK hσ in
theorem isInnerAut_conj_fieldActor_mul_inv (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (δ : K ≃+* K) :
    IsInnerAut (MulAut.conj g * fieldActor σ δ * (MulAut.conj g)⁻¹ * (fieldActor σ δ)⁻¹) := by
  refine ⟨g * fieldActor σ δ g⁻¹, ?_⟩
  rw [map_mul, ← mul_mulAutConj_mul_inv, map_inv]
  group

theorem stdPinnedTriality_stable : (stdPinnedTriality σ).Stable := by
  refine ⟨⟨fun d hd α => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hd
    exact ⟨α y, (mul_mulAutConj_mul_inv α y).symm⟩
  · rintro α _ ⟨ε, rfl⟩ h1
    obtain ⟨g, hg⟩ := exists_conj_eq_conj_fieldActor hf hK hσ α
    exact ⟨fieldActor σ ε, ⟨ε, rfl⟩, h1, MulAut.conj g, ⟨g, rfl⟩, hg ε⟩
  · rintro α γ hγ
    exact absurd hγ (Set.notMem_empty γ)
  · rintro α γ φ hγ
    exact absurd hγ (Set.notMem_empty γ)

theorem stdPinnedTriality_separated : (stdPinnedTriality σ).Separated := by
  refine PinnedAut.Separated.of_graph_eq_empty _ rfl ?_ ?_
  · rintro φ - _ ⟨g, rfl⟩
    exact ⟨φ g, (mul_mulAutConj_mul_inv φ g).symm⟩
  · rintro _ ⟨δ, rfl⟩ hmem
    change fieldActor σ δ = 1
    rw [(isInnerAut_fieldActor_iff hf hK hσ).mp hmem, fieldActor_one]

theorem not_isInnerAut_of_trialityHasKind {τ : MulAut (graphFixedRootGroup TwistTag.D4 K
    σ.toRingHom)} {k : AutKind} (hτ : trialityHasKind σ τ k) (hk : k ≠ .inner) :
    ¬ IsInnerAut τ := by
  intro hin
  cases k with
  | inner => exact hk rfl
  | diagonal => exact hτ
  | graph => exact hτ
  | field =>
    obtain ⟨δ, hδ1, -, g, rfl⟩ := hτ
    refine hδ1 ((isInnerAut_fieldActor_iff hf hK hσ).mp ?_)
    have h1 := (isInnerAut_conj_iff (MulAut.conj g)⁻¹ _).mpr hin
    rwa [show (MulAut.conj g)⁻¹ * (MulAut.conj g * fieldActor σ δ * (MulAut.conj g)⁻¹) *
      (MulAut.conj g)⁻¹⁻¹ = fieldActor σ δ by group] at h1
  | graphField =>
    obtain ⟨δ, h3, hc⟩ := hτ
    have hδ : IsInnerAut (fieldActor (t := TwistTag.D4) σ δ) := by
      rw [show fieldActor (t := TwistTag.D4) σ δ =
        (τ * (fieldActor σ δ)⁻¹)⁻¹ * τ by group]
      exact mul_mem (inv_mem hc) hin
    rw [(isInnerAut_fieldActor_iff hf hK hσ).mp hδ, orderOf_one] at h3
    exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)

theorem trialityHasKind_conj (α τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (k : AutKind) : trialityHasKind σ (α * τ * α⁻¹) k ↔ trialityHasKind σ τ k := by
  have key : ∀ (β ρ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      trialityHasKind σ ρ k → trialityHasKind σ (β * ρ * β⁻¹) k := by
    intro β ρ hρ
    cases k with
    | inner => exact (isInnerAut_conj_iff β ρ).mpr hρ
    | diagonal => exact hρ
    | graph => exact hρ
    | field =>
      obtain ⟨δ, hδ1, hcop, g, rfl⟩ := hρ
      obtain ⟨h, hh⟩ := exists_conj_eq_conj_fieldActor hf hK hσ β
      refine ⟨δ, hδ1, hcop, β g * h, ?_⟩
      calc β * (MulAut.conj g * fieldActor σ δ * (MulAut.conj g)⁻¹) * β⁻¹ =
          (β * MulAut.conj g * β⁻¹) * (β * fieldActor σ δ * β⁻¹) *
            (β * MulAut.conj g * β⁻¹)⁻¹ := by group
        _ = MulAut.conj (β g * h) * fieldActor σ δ * (MulAut.conj (β g * h))⁻¹ := by
          rw [mul_mulAutConj_mul_inv, hh, map_mul]
          group
    | graphField =>
      obtain ⟨δ, h3, hc⟩ := hρ
      refine ⟨δ, h3, ?_⟩
      obtain ⟨h, hh⟩ := exists_conj_eq_conj_fieldActor hf hK hσ β
      have h1 := (isInnerAut_conj_iff β _).mpr hc
      have h2 := isInnerAut_conj_fieldActor_mul_inv h δ
      rw [← hh] at h2
      rw [show β * ρ * β⁻¹ * (fieldActor σ δ)⁻¹ = β * (ρ * (fieldActor σ δ)⁻¹) * β⁻¹ *
        (β * fieldActor σ δ * β⁻¹ * (fieldActor σ δ)⁻¹) by group]
      exact mul_mem h1 h2
  refine ⟨fun h => ?_, key α τ⟩
  have h2 := key α⁻¹ _ h
  rwa [show α⁻¹ * (α * τ * α⁻¹) * α⁻¹⁻¹ = τ by group] at h2

theorem trialityHasKind_unique {τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    {k₁ k₂ : AutKind} (h₁ : trialityHasKind σ τ k₁) (h₂ : trialityHasKind σ τ k₂) :
    k₁ = k₂ := by
  have hfg : ∀ {ρ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)},
      trialityHasKind σ ρ .field → ¬ trialityHasKind σ ρ .graphField := by
    rintro ρ ⟨δ, -, hcop, g, rfl⟩ ⟨ε, h3, hc⟩
    have h1 := isInnerAut_conj_fieldActor_mul_inv g δ
    have h2 : IsInnerAut (fieldActor (t := TwistTag.D4) σ (δ * ε⁻¹)) := by
      have hinv : fieldActor (t := TwistTag.D4) σ ε⁻¹ = (fieldActor σ ε)⁻¹ :=
        map_inv (fieldActorHom (t := TwistTag.D4) σ) ε
      rw [fieldActor_mul, hinv,
        show fieldActor σ δ * (fieldActor σ ε)⁻¹ =
          (MulAut.conj g * fieldActor σ δ * (MulAut.conj g)⁻¹ * (fieldActor σ δ)⁻¹)⁻¹ *
            (MulAut.conj g * fieldActor σ δ * (MulAut.conj g)⁻¹ * (fieldActor σ ε)⁻¹) by group]
      exact mul_mem (inv_mem h1) hc
    have h4 := (isInnerAut_fieldActor_iff hf hK hσ).mp h2
    rw [mul_inv_eq_one] at h4
    subst h4
    exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) h3) (by norm_num)
  cases k₁ <;> cases k₂ <;> first
    | rfl
    | exact absurd h₁ (not_isInnerAut_of_trialityHasKind hf hK hσ h₂ (by decide))
    | exact absurd h₂ (not_isInnerAut_of_trialityHasKind hf hK hσ h₁ (by decide))
    | exact h₁.elim
    | exact h₂.elim
    | exact absurd h₂ (hfg h₁)
    | exact absurd h₁ (hfg h₂)

end NormalForm

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (σ) in
@[expose] def InducesKindTriality (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    ∃ hx : x ∈ Subgroup.normalizer (L : Set G), trialityHasKind σ (inducedAutHom L e ⟨x, hx⟩) k

variable (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
include hf hK hσ

theorem inducesKindTriality_iff
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (x : G)
    (k : AutKind) :
    InducesKindTriality σ L x k ↔
      ∃ hx : x ∈ Subgroup.normalizer (L : Set G),
        trialityHasKind σ (inducedAutHom L e ⟨x, hx⟩) k := by
  constructor
  · rintro ⟨e', hx, h⟩
    refine ⟨hx, ?_⟩
    rw [inducedAutHom_eq_conj L e' e]
    exact (trialityHasKind_conj hf hK hσ _ _ k).mpr h
  · rintro ⟨hx, h⟩
    exact ⟨e, hx, h⟩

theorem inducesKindTriality_unique {x : G} {k₁ k₂ : AutKind}
    (h₁ : InducesKindTriality σ L x k₁) (h₂ : InducesKindTriality σ L x k₂) : k₁ = k₂ := by
  obtain ⟨e, hx, h₁⟩ := h₁
  obtain ⟨hx', h₂⟩ := (inducesKindTriality_iff L hf hK hσ e x k₂).mp h₂
  exact trialityHasKind_unique hf hK hσ h₁ h₂

theorem InducesKindTriality.inducesOuterTheta {x : G} {k : AutKind}
    (h : InducesKindTriality σ L x k) (hk : k ≠ .inner) : InducesOuterTheta x L := by
  obtain ⟨e, hx, h⟩ := h
  exact (not_isInnerAut_inducedAutHom_iff L e hx).mp
    (not_isInnerAut_of_trialityHasKind hf hK hσ h hk)

end Induced

end CFSG.RankThree.PartTwo.KFacts
