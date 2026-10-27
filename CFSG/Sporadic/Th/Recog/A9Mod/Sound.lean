module

public import CFSG.Sporadic.Th.Recog.A9Mod.Bits

public section

local instance (priority := high) CFSG.Sporadic.Th.Recog.A9Mod.instAddCommGroupZMod2Sound :
    AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

namespace CFSG.Sporadic.Th.Recog.A9Mod

open CFSG.Sporadic.Th.Max3

theorem eltG_pow_eight : eltG ^ 8 = eltG⁻¹ := by decide +kernel

theorem eltS₁_pow_five : eltS₁ ^ 5 = eltS₁⁻¹ := by decide +kernel

theorem eltS₂_inv : eltS₂⁻¹ = eltS₂ := by decide +kernel

theorem eltS₃_sq : eltS₃ ^ 2 = eltS₃⁻¹ := by decide +kernel

theorem eltS₁_conj : eltS₁ * eltG * eltS₁⁻¹ = eltG * eltG := by decide +kernel

theorem relsK1_letters : ∀ r ∈ relsK1, ∀ i ∈ r, i < 8 ∧ i % 4 < 2 := by decide +kernel

theorem relsK2_letters : ∀ r ∈ relsK2, ∀ i ∈ r, i < 8 ∧ i % 4 < 3 := by decide +kernel

theorem relsA9_letters : ∀ r ∈ relsA9, ∀ i ∈ r, i < 8 ∧ i % 4 < 4 := by decide +kernel

theorem wordH_letters : ∀ i ∈ wordH, i < 8 ∧ i % 4 < 2 := by decide +kernel

theorem wordsL_letters : ∀ p ∈ wordsL,
    (∀ i ∈ p.1, i < 8 ∧ i % 4 < 3) ∧ (∀ i ∈ p.2, i < 8 ∧ i % 4 < 3) := by decide +kernel

theorem wordA_letters : ∀ i ∈ wordA, i < 8 ∧ i % 4 < 4 := by decide +kernel

theorem wordB_letters : ∀ i ∈ wordB, i < 8 ∧ i % 4 < 4 := by decide +kernel

theorem wordB'_letters : ∀ i ∈ wordB', i < 8 ∧ i % 4 < 4 := by decide +kernel

variable (σ : alternatingGroup (Fin 9) →* Module.End (ZMod 2) V8)

@[expose] def ConjToTarget : Prop :=
  ∃ p : Array ℕ, Function.Injective (toLin p) ∧
    ((toLin p * σ (evalA wordA) = toLin B1M * toLin p ∧
        toLin p * σ (evalA wordB) = toLin B2M * toLin p) ∨
      (toLin p * σ (evalA wordA) = toLin B1M * toLin p ∧
        toLin p * σ (evalA wordB') = toLin B2M * toLin p) ∨
      (toLin p * σ (evalA wordA) = toLin P8A * toLin p ∧
        toLin p * σ (evalA wordB) = toLin P8B * toLin p))

theorem intertwine (τ : alternatingGroup (Fin 9) →* Module.End (ZMod 2) V8)
    (P : Module.End (ZMod 2) V8) (a b : alternatingGroup (Fin 9))
    (hab : Subgroup.closure ({a, b} : Set (alternatingGroup (Fin 9))) = ⊤)
    (ha : P * σ a = τ a * P) (hb : P * σ b = τ b * P) (x : alternatingGroup (Fin 9)) :
    P * σ x = τ x * P := by
  have hx : x ∈ Subgroup.closure ({a, b} : Set (alternatingGroup (Fin 9))) :=
    hab ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ha
    · exact hb
  | one => rw [map_one, map_one, mul_one, one_mul]
  | mul y z _ _ hy hz =>
    rw [map_mul, map_mul, ← mul_assoc, hy, mul_assoc (τ y) P (σ z), hz, ← mul_assoc]
  | inv y _ hy =>
    calc P * σ y⁻¹ = τ y⁻¹ * τ y * P * σ y⁻¹ := by
          rw [← map_mul, inv_mul_cancel, map_one, one_mul]
      _ = τ y⁻¹ * (τ y * P) * σ y⁻¹ := by rw [mul_assoc (τ y⁻¹) (τ y) P]
      _ = τ y⁻¹ * (P * σ y) * σ y⁻¹ := by rw [hy]
      _ = τ y⁻¹ * P * (σ y * σ y⁻¹) := by simp only [mul_assoc]
      _ = τ y⁻¹ * P := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]

@[expose] noncomputable def endHom {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : alternatingGroup (Fin 9) →* (V ≃ₗ[ZMod 2] V)) :
    alternatingGroup (Fin 9) →* Module.End (ZMod 2) V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ

theorem endHom_apply {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : alternatingGroup (Fin 9) →* (V ≃ₗ[ZMod 2] V)) (x : alternatingGroup (Fin 9)) (v : V) :
    endHom ρ x v = ρ x v :=
  rfl

theorem endHom_rho8p_a : endHom rho8p ⟨aPerm, aPerm_mem⟩ = toLin P8A :=
  LinearMap.ext fun v => by rw [endHom_apply, P8A_spec, LinearEquiv.coe_coe]

theorem endHom_rho8p_b : endHom rho8p ⟨bPerm, bPerm_mem⟩ = toLin P8B :=
  LinearMap.ext fun v => by rw [endHom_apply, P8B_spec, LinearEquiv.coe_coe]

end CFSG.Sporadic.Th.Recog.A9Mod
