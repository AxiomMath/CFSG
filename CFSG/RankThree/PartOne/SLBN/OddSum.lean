module

public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.RankThree.PartOne.SLBN

variable {Q : Type*} [CommGroup Q]

theorem apply_apply_of_mul_self_eq_one {σ : MulAut Q} (h : σ * σ = 1) (y : Q) : σ (σ y) = y := by
  have := congrArg (fun τ : MulAut Q => τ y) h
  simpa using this

theorem alt3 (a b c d : Q) : (a * b)⁻¹ * (b * c) * (c * d)⁻¹ = (a * d)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem alt5 (a b c d e f : Q) :
    (a * b)⁻¹ * (b * c) * (c * d)⁻¹ * (d * e) * (e * f)⁻¹ = (a * f)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem inv_sq_of_pow_three {x : Q} (hx : x ^ 3 = 1) : (x * x)⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_three']; exact hx)

theorem exists_prod_fixed_three (hQ : ∀ x : Q, x ^ 3 = 1) (σ₁ σ₂ σ₃ : MulAut Q) (h₁ : σ₁ * σ₁ = 1)
    (h₂ : σ₂ * σ₂ = 1) (h₃ : σ₃ * σ₃ = 1) (hp : σ₁ * σ₂ * σ₃ = 1) (x : Q) :
    ∃ c₁ c₂ c₃ : Q, σ₁ c₁ = c₁ ∧ σ₂ c₂ = c₂ ∧ σ₃ c₃ = c₃ ∧ x = c₁ * c₂ * c₃ := by
  obtain ⟨y₃, hy₃⟩ : ∃ y : Q, y = x := ⟨x, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y : Q, y = σ₃ y₃ := ⟨_, rfl⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y : Q, y = σ₂ y₂ := ⟨_, rfl⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y : Q, y = σ₁ y₁ := ⟨_, rfl⟩
  have h0 : y₀ = x := by
    have := congrArg (fun τ : MulAut Q => τ x) hp
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    rw [hy₀, hy₁, hy₂, hy₃]
    exact this
  have e1 : σ₁ y₀ = y₁ := by rw [hy₀]; exact apply_apply_of_mul_self_eq_one h₁ y₁
  have e2 : σ₂ y₁ = y₂ := by rw [hy₁]; exact apply_apply_of_mul_self_eq_one h₂ y₂
  have e3 : σ₃ y₂ = y₃ := by rw [hy₂]; exact apply_apply_of_mul_self_eq_one h₃ y₃
  refine ⟨(y₀ * y₁)⁻¹, y₁ * y₂, (y₂ * y₃)⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [map_inv, map_mul, e1, ← hy₀, mul_comm y₁ y₀]
  · rw [map_mul, ← hy₁, e2, mul_comm]
  · rw [map_inv, map_mul, ← hy₂, e3, mul_comm]
  · rw [alt3, h0, hy₃, inv_sq_of_pow_three (hQ x)]

theorem exists_prod_fixed_five (hQ : ∀ x : Q, x ^ 3 = 1) (σ₁ σ₂ σ₃ σ₄ σ₅ : MulAut Q)
    (h₁ : σ₁ * σ₁ = 1) (h₂ : σ₂ * σ₂ = 1) (h₃ : σ₃ * σ₃ = 1) (h₄ : σ₄ * σ₄ = 1)
    (h₅ : σ₅ * σ₅ = 1) (hp : σ₁ * σ₂ * σ₃ * σ₄ * σ₅ = 1) (x : Q) :
    ∃ c₁ c₂ c₃ c₄ c₅ : Q, σ₁ c₁ = c₁ ∧ σ₂ c₂ = c₂ ∧ σ₃ c₃ = c₃ ∧ σ₄ c₄ = c₄ ∧ σ₅ c₅ = c₅ ∧
      x = c₁ * c₂ * c₃ * c₄ * c₅ := by
  obtain ⟨y₅, hy₅⟩ : ∃ y : Q, y = x := ⟨x, rfl⟩
  obtain ⟨y₄, hy₄⟩ : ∃ y : Q, y = σ₅ y₅ := ⟨_, rfl⟩
  obtain ⟨y₃, hy₃⟩ : ∃ y : Q, y = σ₄ y₄ := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y : Q, y = σ₃ y₃ := ⟨_, rfl⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y : Q, y = σ₂ y₂ := ⟨_, rfl⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y : Q, y = σ₁ y₁ := ⟨_, rfl⟩
  have h0 : y₀ = x := by
    have := congrArg (fun τ : MulAut Q => τ x) hp
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    rw [hy₀, hy₁, hy₂, hy₃, hy₄, hy₅]
    exact this
  have e1 : σ₁ y₀ = y₁ := by rw [hy₀]; exact apply_apply_of_mul_self_eq_one h₁ y₁
  have e2 : σ₂ y₁ = y₂ := by rw [hy₁]; exact apply_apply_of_mul_self_eq_one h₂ y₂
  have e3 : σ₃ y₂ = y₃ := by rw [hy₂]; exact apply_apply_of_mul_self_eq_one h₃ y₃
  have e4 : σ₄ y₃ = y₄ := by rw [hy₃]; exact apply_apply_of_mul_self_eq_one h₄ y₄
  have e5 : σ₅ y₄ = y₅ := by rw [hy₄]; exact apply_apply_of_mul_self_eq_one h₅ y₅
  refine ⟨(y₀ * y₁)⁻¹, y₁ * y₂, (y₂ * y₃)⁻¹, y₃ * y₄, (y₄ * y₅)⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_inv, map_mul, e1, ← hy₀, mul_comm y₁ y₀]
  · rw [map_mul, ← hy₁, e2, mul_comm]
  · rw [map_inv, map_mul, ← hy₂, e3, mul_comm]
  · rw [map_mul, ← hy₃, e4, mul_comm]
  · rw [map_inv, map_mul, ← hy₄, e5, mul_comm]
  · rw [alt5, h0, hy₅, inv_sq_of_pow_three (hQ x)]

theorem card_le_of_five_fixed [Finite Q] (hQ : ∀ x : Q, x ^ 3 = 1)
    (σ₁ σ₂ σ₃ σ₄ σ₅ : MulAut Q) (h₁ : σ₁ * σ₁ = 1) (h₂ : σ₂ * σ₂ = 1) (h₃ : σ₃ * σ₃ = 1)
    (h₄ : σ₄ * σ₄ = 1) (h₅ : σ₅ * σ₅ = 1) (hp : σ₁ * σ₂ * σ₃ * σ₄ * σ₅ = 1)
    (f₁ : Nat.card {v : Q | σ₁ v = v} ≤ 3) (f₂ : Nat.card {v : Q | σ₂ v = v} ≤ 3)
    (f₃ : Nat.card {v : Q | σ₃ v = v} ≤ 3) (f₄ : Nat.card {v : Q | σ₄ v = v} ≤ 3)
    (f₅ : Nat.card {v : Q | σ₅ v = v} ≤ 3) : Nat.card Q ≤ 3 ^ 5 := by
  let F : {v : Q | σ₁ v = v} × {v : Q | σ₂ v = v} × {v : Q | σ₃ v = v} ×
      {v : Q | σ₄ v = v} × {v : Q | σ₅ v = v} → Q :=
    fun m => (m.1 : Q) * m.2.1 * m.2.2.1 * m.2.2.2.1 * m.2.2.2.2
  have hF : Function.Surjective F := by
    intro x
    obtain ⟨c₁, c₂, c₃, c₄, c₅, e₁, e₂, e₃, e₄, e₅, hx⟩ :=
      exists_prod_fixed_five hQ σ₁ σ₂ σ₃ σ₄ σ₅ h₁ h₂ h₃ h₄ h₅ hp x
    exact ⟨(⟨c₁, e₁⟩, ⟨c₂, e₂⟩, ⟨c₃, e₃⟩, ⟨c₄, e₄⟩, ⟨c₅, e₅⟩), hx.symm⟩
  have := Nat.card_le_card_of_surjective F hF
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod] at this
  calc Nat.card Q ≤ Nat.card {v : Q | σ₁ v = v} * (Nat.card {v : Q | σ₂ v = v} *
        (Nat.card {v : Q | σ₃ v = v} * (Nat.card {v : Q | σ₄ v = v} *
          Nat.card {v : Q | σ₅ v = v}))) := this
    _ ≤ 3 * (3 * (3 * (3 * 3))) := by gcongr
    _ = 3 ^ 5 := by norm_num

end CFSG.RankThree.PartOne.SLBN
