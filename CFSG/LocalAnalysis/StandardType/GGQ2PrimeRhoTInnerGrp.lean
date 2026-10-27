module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.GGQ2Prime

open Subgroup
open scoped commutatorElement

private theorem rhoTInner_comm_mul_central_left {H : Type*} [Group H] {x y z : H}
    (hz : z ∈ center H) : ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have h : z * y * z⁻¹ = y := by rw [← mem_center_iff.1 hz y]; group
  rw [commutatorElement_def, commutatorElement_def]
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

private theorem rhoTInner_comm_mul_central_right {H : Type*} [Group H] {x y w : H}
    (hw : w ∈ center H) : ⁅x, y * w⁆ = ⁅x, y⁆ := by
  have h : w * x⁻¹ * w⁻¹ = x⁻¹ := by rw [← mem_center_iff.1 hw x⁻¹]; group
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (y * w) * x⁻¹ * (y * w)⁻¹ = x * y * (w * x⁻¹ * w⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

theorem rhoTInner_comm_of_conj {H : Type*} [Group H] {a v s z₁ z₂ : H} {j : ℤ}
    (hz₁ : z₁ ∈ center H) (hz₂ : z₂ ∈ center H) (hc : ⁅a, v⁆ ∈ center H) (ha3 : a ^ 3 = 1)
    (h₁ : s * a * s⁻¹ = a⁻¹ * z₁) (h₂ : s * v * s⁻¹ = v * a ^ j * z₂) : a * v = v * a := by
  have hcc : s * ⁅a, v⁆ * s⁻¹ = ⁅a, v⁆ := by
    rw [mem_center_iff.1 hc s]; group
  have hmap : s * ⁅a, v⁆ * s⁻¹ = ⁅s * a * s⁻¹, s * v * s⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  rw [hmap, h₁, h₂, rhoTInner_comm_mul_central_left hz₁, rhoTInner_comm_mul_central_right hz₂]
    at hcc
  have h3 : ⁅a⁻¹, v * a ^ j⁆ = a⁻¹ * v * a * v⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h3, commutatorElement_def] at hcc
  have e : a⁻¹ * v * a = a * v * a⁻¹ := by
    calc a⁻¹ * v * a = a⁻¹ * v * a * v⁻¹ * v := by group
      _ = a * v * a⁻¹ * v⁻¹ * v := by rw [hcc]
      _ = a * v * a⁻¹ := by group
  have e2 : a * a * v = v * (a * a) := by
    calc a * a * v = a * (a * v * a⁻¹) * a := by group
      _ = a * (a⁻¹ * v * a) * a := by rw [e]
      _ = v * (a * a) := by group
  have hinv : a⁻¹ = a * a := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact ha3)
  rw [← hinv] at e2
  calc a * v = a * (v * a⁻¹) * a := by group
    _ = a * (a⁻¹ * v) * a := by rw [e2]
    _ = v * a := by group

theorem rhoTInner_mem_zpowers_of_reflection {B : Type*} [Group B] [Finite B] [IsMulCommutative B]
    (hB3 : ∀ b : B, b ^ 3 = 1) {φ : MulAut B}
    (hcard : Nat.card {b : B // φ b = b} * 3 = Nat.card B) (b v : B) (hb : φ b * b⁻¹ ≠ 1) :
    φ v * v⁻¹ ∈ zpowers (φ b * b⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let δ : B →* B := MonoidHom.mk' (fun c => φ c * c⁻¹) fun c d => by
    simp only [map_mul, mul_inv_rev]
    calc φ c * φ d * (d⁻¹ * c⁻¹) = φ c * (φ d * d⁻¹) * c⁻¹ := by group
      _ = φ c * (c⁻¹ * (φ d * d⁻¹)) := by rw [mul_assoc, mul_comm' (φ d * d⁻¹) c⁻¹]
      _ = φ c * c⁻¹ * (φ d * d⁻¹) := by group
  have hker : Nat.card δ.ker = Nat.card {b : B // φ b = b} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun c => by
      change φ c * c⁻¹ = 1 ↔ φ c = c
      exact mul_inv_eq_one)
  have hmul := card_ker_mul_card_range δ
  have hpos : 0 < Nat.card {b : B // φ b = b} := by
    rw [← hker]; exact Nat.card_pos
  have hrange : Nat.card δ.range = 3 := by
    rw [hker] at hmul
    exact Nat.eq_of_mul_eq_mul_left hpos (hmul.trans hcard.symm)
  have hd3 : (φ b * b⁻¹) ^ 3 = 1 := by
    have : (δ b) ^ 3 = 1 := by rw [← map_pow, hB3, map_one]
    exact this
  have hord : orderOf (φ b * b⁻¹) = 3 := orderOf_eq_prime hd3 hb
  have hle : zpowers (φ b * b⁻¹) ≤ δ.range := zpowers_le.2 ⟨b, rfl⟩
  have hzcard : Nat.card (zpowers (φ b * b⁻¹)) = 3 := by rw [Nat.card_zpowers, hord]
  have heq : zpowers (φ b * b⁻¹) = δ.range :=
    eq_of_le_of_card_ge hle (by rw [hzcard, hrange])
  rw [heq]
  exact ⟨v, rfl⟩

end CFSG.GGQ2Prime
