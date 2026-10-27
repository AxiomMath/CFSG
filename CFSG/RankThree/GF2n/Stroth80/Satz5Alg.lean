module

public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80.Satz5

theorem commutator_relation {G : Type*} [Group G] (a b c x y zz v k₁ k₂ k₃ k₄ κ κ' : G)
    (hab : a * b = b * a * c)
    (hax : a * x * a⁻¹ = x * zz * k₁) (hbx : b * x * b⁻¹ = x * y * k₂)
    (hay : a * y * a⁻¹ = y * v * k₃) (hbz : b * zz * b⁻¹ = zz * v * k₄)
    (hzy : zz * y = y * zz * κ) (hcx : c * x * c⁻¹ = x * κ')
    (hak₂ : a * k₂ * a⁻¹ = k₂) (haκ' : a * κ' * a⁻¹ = κ')
    (hbk₁ : b * k₁ * b⁻¹ = k₁) (hbκ' : b * κ' * b⁻¹ = κ')
    (hk₁y : k₁ * y = y * k₁) (hk₁v : k₁ * v = v * k₁) (hκv : κ * v = v * κ)
    (hk₂zz : k₂ * zz = zz * k₂) (hk₂v : k₂ * v = v * k₂) :
    κ * k₁ * k₃ * k₂ = k₂ * k₄ * k₁ * κ' := by
  have hL : a * b * x * (a * b)⁻¹ = x * zz * k₁ * (y * v * k₃) * k₂ := by
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = a * (x * y * k₂) * a⁻¹ := by rw [hbx]
      _ = (a * x * a⁻¹) * (a * y * a⁻¹) * (a * k₂ * a⁻¹) := by group
      _ = (x * zz * k₁) * (y * v * k₃) * k₂ := by rw [hax, hay, hak₂]
  have hR : a * b * x * (a * b)⁻¹ = x * y * k₂ * (zz * v * k₄) * k₁ * κ' := by
    calc a * b * x * (a * b)⁻¹ = (b * a * c) * x * (b * a * c)⁻¹ := by rw [hab]
      _ = b * a * (c * x * c⁻¹) * a⁻¹ * b⁻¹ := by group
      _ = b * (a * (x * κ') * a⁻¹) * b⁻¹ := by rw [hcx]; group
      _ = b * ((a * x * a⁻¹) * (a * κ' * a⁻¹)) * b⁻¹ := by group
      _ = b * ((x * zz * k₁) * κ') * b⁻¹ := by rw [hax, haκ']
      _ = (b * x * b⁻¹) * (b * zz * b⁻¹) * (b * k₁ * b⁻¹) * (b * κ' * b⁻¹) := by group
      _ = (x * y * k₂) * (zz * v * k₄) * k₁ * κ' := by rw [hbx, hbz, hbk₁, hbκ']
  have hE := hL.symm.trans hR
  have hlhs : x * zz * k₁ * (y * v * k₃) * k₂ = x * y * zz * v * (κ * k₁ * k₃ * k₂) := by
    calc x * zz * k₁ * (y * v * k₃) * k₂ = x * zz * (k₁ * y) * v * k₃ * k₂ := by
          simp only [mul_assoc]
      _ = x * zz * (y * k₁) * v * k₃ * k₂ := by rw [hk₁y]
      _ = x * zz * y * (k₁ * v) * k₃ * k₂ := by simp only [mul_assoc]
      _ = x * zz * y * (v * k₁) * k₃ * k₂ := by rw [hk₁v]
      _ = x * (zz * y) * v * k₁ * k₃ * k₂ := by simp only [mul_assoc]
      _ = x * (y * zz * κ) * v * k₁ * k₃ * k₂ := by rw [hzy]
      _ = x * y * zz * (κ * v) * k₁ * k₃ * k₂ := by simp only [mul_assoc]
      _ = x * y * zz * (v * κ) * k₁ * k₃ * k₂ := by rw [hκv]
      _ = x * y * zz * v * (κ * k₁ * k₃ * k₂) := by simp only [mul_assoc]
  have hrhs : x * y * k₂ * (zz * v * k₄) * k₁ * κ' = x * y * zz * v * (k₂ * k₄ * k₁ * κ') := by
    calc x * y * k₂ * (zz * v * k₄) * k₁ * κ' = x * y * (k₂ * zz) * v * k₄ * k₁ * κ' := by
          simp only [mul_assoc]
      _ = x * y * (zz * k₂) * v * k₄ * k₁ * κ' := by rw [hk₂zz]
      _ = x * y * zz * (k₂ * v) * k₄ * k₁ * κ' := by simp only [mul_assoc]
      _ = x * y * zz * (v * k₂) * k₄ * k₁ * κ' := by rw [hk₂v]
      _ = x * y * zz * v * (k₂ * k₄ * k₁ * κ') := by simp only [mul_assoc]
  rw [hlhs, hrhs] at hE
  exact mul_left_cancel hE

theorem elimination {K : Type*} [Field K] (h2 : (2 : K) = 0) {ν : K} (hν0 : ν ≠ 0)
    (hν1 : ν ≠ 1) (F₁ Fν H₁ Hν : K → K)
    (e11 : ∃ κ : K, ∀ s, 1 * 1 * s ^ 2 + F₁ (1 * s) + H₁ (1 * s) = κ * s)
    (eν1 : ∃ κ : K, ∀ s, ν * 1 * s ^ 2 + Fν (1 * s) + H₁ (ν * s) = κ * s)
    (e1ν : ∃ κ : K, ∀ s, 1 * ν * s ^ 2 + F₁ (ν * s) + Hν (1 * s) = κ * s)
    (eνν : ∃ κ : K, ∀ s, ν * ν * s ^ 2 + Fν (ν * s) + Hν (ν * s) = κ * s) : False := by
  obtain ⟨k11, h11⟩ := e11
  obtain ⟨kν1, hν1'⟩ := eν1
  obtain ⟨k1ν, h1ν⟩ := e1ν
  obtain ⟨kνν, hνν⟩ := eνν
  have key : ∀ s₀ : K, (ν ^ 4 + ν ^ 2) * s₀ ^ 2 =
      (k11 * ν ^ 2 + (kν1 + k1ν) * ν + kνν) * s₀ := by
    intro s₀
    have a1 := h11 (ν ^ 2 * s₀)
    have a2 := hν1' (ν * s₀)
    have a3 := h1ν (ν * s₀)
    have a4 := hνν s₀
    simp only [one_mul] at a1 a2 a3 a4
    have e1 : ν * (ν * s₀) = ν ^ 2 * s₀ := by ring
    rw [e1] at a2 a3
    linear_combination a1 + a2 + a3 + a4 + (-(F₁ (ν ^ 2 * s₀) + H₁ (ν ^ 2 * s₀) + Fν (ν * s₀)
      + Hν (ν * s₀) + ν ^ 3 * s₀ ^ 2)) * h2
  have k1 := key 1
  have kν := key ν
  have hne : ν ^ 3 * (ν + 1) ^ 3 ≠ 0 := by
    have : ν + 1 ≠ 0 := fun h => hν1 (by linear_combination h - h2)
    exact mul_ne_zero (pow_ne_zero 3 hν0) (pow_ne_zero 3 this)
  apply hne
  linear_combination kν - ν * k1 + (2 * ν ^ 5 + ν ^ 4 + ν ^ 3) * h2

theorem exists_ne_zero_one {K : Type*} [Field K] (hK : 2 < Nat.card K) :
    ∃ ν : K, ν ≠ 0 ∧ ν ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hinj : Function.Injective (fun x : K => decide (x = 0)) := by
    intro x y hxy
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · rw [hx, hy]
    · exact absurd hxy (by simp [hx, hy])
    · exact absurd hxy (by simp [hx, hy])
    · rw [hcon x hx, hcon y hy]
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

end CFSG.RankThree.GF2n.Stroth80.Satz5
