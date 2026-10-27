module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructNorm

public section

namespace CFSG.Quasithin.H13.F431.D4q.Struct

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


section Center

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem center_eq_bot : Subgroup.center (Cm σ) = ⊥ :=
  exceptional_fixed_center_trivial TwistTag.D4 K σ

theorem conj_injective : Function.Injective (MulAut.conj : Cm σ →* MulAut (Cm σ)) := by
  intro a b h
  have hc : b⁻¹ * a ∈ Subgroup.center (Cm σ) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 : (MulAut.conj (b⁻¹ * a) : MulAut (Cm σ)) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h3 := congrArg (fun φ : MulAut (Cm σ) => φ y) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    calc y * (b⁻¹ * a) = (b⁻¹ * a * y * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by rw [h3]
      _ = (b⁻¹ * a) * y := by group
  rw [center_eq_bot σ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

end Center

section Theta

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hf hK hσ

theorem exists_theta : ∃ Θ : MulAut (Cm σ) →* (K ≃+* K),
    (∀ (α : MulAut (Cm σ)) (g : Cm σ) (δ : K ≃+* K),
      α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
    (∀ α : MulAut (Cm σ), ∃ (g : Cm σ) (δ : K ≃+* K), α = MulAut.conj g * fieldActor σ δ) ∧
    Θ.ker = (MulAut.conj : Cm σ →* MulAut (Cm σ)).range := by
  obtain ⟨-, hex, ⟨Θ, h1, -, h3, -⟩, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  refine ⟨Θ, h1, fun α => ?_, h3⟩
  obtain ⟨⟨g, δ⟩, h, -⟩ := hex α
  exact ⟨g, δ, h⟩

noncomputable def theta : MulAut (Cm σ) →* (K ≃+* K) := (exists_theta σ hf hK hσ).choose

theorem theta_conj_fieldActor (g : Cm σ) (δ : K ≃+* K) :
    theta σ hf hK hσ (MulAut.conj g * fieldActor σ δ) = δ :=
  (exists_theta σ hf hK hσ).choose_spec.1 _ g δ rfl

theorem theta_ker : (theta σ hf hK hσ).ker = (MulAut.conj : Cm σ →* MulAut (Cm σ)).range :=
  (exists_theta σ hf hK hσ).choose_spec.2.2

theorem exists_conj_fieldActor (α : MulAut (Cm σ)) :
    ∃ g : Cm σ, α = MulAut.conj g * fieldActor σ (theta σ hf hK hσ α) := by
  obtain ⟨g, δ, h⟩ := (exists_theta σ hf hK hσ).choose_spec.2.1 α
  have hθ : theta σ hf hK hσ α = δ := by
    rw [h]
    exact theta_conj_fieldActor σ hf hK hσ g δ
  exact ⟨g, hθ ▸ h⟩

variable {Kb : Subgroup (MulAut (Cm σ))}
  (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)

include hinn in
theorem fieldActor_mem_iff (δ : K ≃+* K) :
    fieldActor σ δ ∈ Kb ↔ δ ∈ Kb.map (theta σ hf hK hσ) := by
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    have := theta_conj_fieldActor σ hf hK hσ 1 δ
    rwa [map_one, one_mul] at this
  · rintro ⟨α, hα, hαδ⟩
    obtain ⟨g, hg⟩ := exists_conj_fieldActor σ hf hK hσ α
    rw [hαδ] at hg
    have : fieldActor σ δ = (MulAut.conj g)⁻¹ * α := by rw [hg]; group
    rw [this]
    exact Kb.mul_mem (Kb.inv_mem (hinn ⟨g, rfl⟩)) hα

include hinn in
theorem conj_mul_fieldActor_mem_iff (g : Cm σ) (δ : K ≃+* K) :
    MulAut.conj g * fieldActor σ δ ∈ Kb ↔ δ ∈ Kb.map (theta σ hf hK hσ) := by
  rw [← fieldActor_mem_iff σ hf hK hσ hinn]
  constructor
  · intro h
    have h' := Kb.mul_mem (Kb.inv_mem (hinn ⟨g, rfl⟩)) h
    rwa [inv_mul_cancel_left] at h'
  · intro h
    exact Kb.mul_mem (hinn ⟨g, rfl⟩) h

include hinn in
theorem card_eq_of_inn_le :
    Nat.card ↥Kb = Nat.card (Cm σ) * Nat.card ↥(Kb.map (theta σ hf hK hσ)) := by
  let φ := (theta σ hf hK hσ).comp Kb.subtype
  have h := Subgroup.card_ker_mul_card_range φ
  have hr : φ.range = Kb.map (theta σ hf hK hσ) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker.map Kb.subtype = (theta σ hf hK hσ).ker := by
    ext α
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hα
      have hαK : α ∈ Kb := by
        rw [theta_ker σ hf hK hσ] at hα
        exact hinn hα
      exact ⟨⟨α, hαK⟩, hα, rfl⟩
  have e1 : Nat.card φ.ker = Nat.card (Cm σ) := by
    calc Nat.card φ.ker = Nat.card (φ.ker.map Kb.subtype) :=
          Nat.card_congr (φ.ker.equivMapOfInjective Kb.subtype Kb.subtype_injective).toEquiv
      _ = Nat.card (theta σ hf hK hσ).ker := by rw [hker]
      _ = Nat.card (Cm σ) := by
          rw [theta_ker σ hf hK hσ]
          exact (Nat.card_congr (MonoidHom.ofInjective (conj_injective σ)).toEquiv).symm
  rw [← h, e1, hr]

end Theta

end CFSG.Quasithin.H13.F431.D4q.Struct
