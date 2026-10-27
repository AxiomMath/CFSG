module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Pointwise

import Mathlib.Tactic.Group

public section

namespace CFSG.ShultStronglyClosedTI.CentralSection

open Subgroup
open scoped Pointwise

variable {P : Type*} [Group P]

@[expose] def commutatorHom (hc : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ center P) (t : P) : P →* P where
  toFun a := a * t * a⁻¹ * t⁻¹
  map_one' := by group
  map_mul' a b := by
    have hz := mem_center_iff.mp (hc b t)
    change a * b * t * (a * b)⁻¹ * t⁻¹ = a * t * a⁻¹ * t⁻¹ * (b * t * b⁻¹ * t⁻¹)
    calc a * b * t * (a * b)⁻¹ * t⁻¹ = a * (b * t * b⁻¹ * t⁻¹) * t * a⁻¹ * t⁻¹ := by group
      _ = b * t * b⁻¹ * t⁻¹ * a * t * a⁻¹ * t⁻¹ := by rw [hz a]
      _ = b * t * b⁻¹ * t⁻¹ * (a * t * a⁻¹ * t⁻¹) := by group
      _ = a * t * a⁻¹ * t⁻¹ * (b * t * b⁻¹ * t⁻¹) := (hz _).symm

section commutatorHom

variable (hc : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ center P)

theorem commutatorHom_apply (t a : P) : commutatorHom hc t a = a * t * a⁻¹ * t⁻¹ :=
  rfl

theorem commutatorHom_eq_one_iff {t a : P} :
    commutatorHom hc t a = 1 ↔ a ∈ centralizer {t} := by
  rw [commutatorHom_apply, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, mem_centralizer_singleton_iff]

theorem ker_commutatorHom (t : P) : (commutatorHom hc t).ker = centralizer {t} := by
  ext a
  exact commutatorHom_eq_one_iff hc

theorem commutatorHom_eq_one_of_mem_center {t z : P} (hz : z ∈ center P) :
    commutatorHom hc t z = 1 := by
  rw [commutatorHom_apply, ← mem_center_iff.mp hz t]
  group

theorem map_commutatorHom {t : P} (σ : P ≃* P) (ht : σ t = t) (a : P) :
    σ (commutatorHom hc t a) = commutatorHom hc t (σ a) := by
  simp only [commutatorHom_apply, map_mul, map_inv, ht]

end commutatorHom

theorem mul_sq_eq (hc : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ center P) (a b : P) :
    (a * b) ^ 2 = b * a * b⁻¹ * a⁻¹ * a ^ 2 * b ^ 2 := by
  have hz := mem_center_iff.mp (hc b a)
  calc (a * b) ^ 2 = a * (b * a * b⁻¹ * a⁻¹) * a * b * b := by rw [sq]; group
    _ = b * a * b⁻¹ * a⁻¹ * a * a * b * b := by rw [hz a]
    _ = b * a * b⁻¹ * a⁻¹ * a ^ 2 * b ^ 2 := by rw [sq, sq]; group

theorem mul_sq_of_mem_center {g z : P} (hz : z ∈ center P) (hz2 : z ^ 2 = 1) :
    (g * z) ^ 2 = g ^ 2 := by
  calc (g * z) ^ 2 = g * (z * g) * z := by rw [sq]; group
    _ = g * (g * z) * z := by rw [← mem_center_iff.mp hz g]
    _ = g ^ 2 * z ^ 2 := by rw [sq, sq]; group
    _ = g ^ 2 := by rw [hz2, mul_one]

theorem card_sup_le_of_le_center {Q T : Subgroup P} (hQ : Q ≤ center P) :
    Nat.card (Q ⊔ T : Subgroup P) ≤ Nat.card Q * Nat.card T := by
  have := normal_of_le_center hQ
  rw [← SetLike.coe_sort_coe, normal_mul]
  exact Set.natCard_mul_le

structure SingerSection {X : Type*} [Group X] (Q T : Subgroup P) (φ : X →* MulAut P) : Prop where
  le_center : Q ≤ center P
  sq_eq_one : ∀ z ∈ Q, z ^ 2 = 1
  commutator_mem : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ Q
  sq_mem : ∀ a : P, a ^ 2 ∈ Q
  comm : ∀ x y : X, x * y = y * x
  map_mem : ∀ x : X, ∀ z ∈ Q, φ x z ∈ Q
  eq_one_of_fixed : ∀ x : X, ∀ z ∈ Q, z ≠ 1 → φ x z = z → x = 1
  exists_map_eq : ∀ z ∈ Q, z ≠ 1 → ∀ z' ∈ Q, z' ≠ 1 → ∃ x : X, φ x z = z'
  fixed : ∀ x : X, ∀ t ∈ T, φ x t = t
  sq_eq_one_of_mem : ∀ t ∈ T, t ^ 2 = 1
  inf_eq_bot : Q ⊓ T = ⊥
  centralizer_eq : ∀ t ∈ T, t ≠ 1 → centralizer {t} = Q ⊔ T

namespace SingerSection

variable {X : Type*} [Group X] {Q T : Subgroup P} {φ : X →* MulAut P}

theorem commutator_mem_center (h : SingerSection Q T φ) (a b : P) :
    a * b * a⁻¹ * b⁻¹ ∈ center P :=
  h.le_center (h.commutator_mem a b)

theorem normal (h : SingerSection Q T φ) : Q.Normal :=
  normal_of_le_center h.le_center

@[expose] def κ (h : SingerSection Q T φ) (t : P) : P →* P :=
  commutatorHom h.commutator_mem_center t

theorem κ_apply (h : SingerSection Q T φ) (t a : P) : h.κ t a = a * t * a⁻¹ * t⁻¹ :=
  rfl

theorem κ_mem (h : SingerSection Q T φ) (t a : P) : h.κ t a ∈ Q :=
  h.commutator_mem a t

theorem κ_eq_one_of_mem (h : SingerSection Q T φ) (t : P) {z : P} (hz : z ∈ Q) : h.κ t z = 1 :=
  commutatorHom_eq_one_of_mem_center _ (h.le_center hz)

theorem κ_eq_one_iff (h : SingerSection Q T φ) {t : P} (ht : t ∈ T) (ht1 : t ≠ 1) {a : P} :
    h.κ t a = 1 ↔ a ∈ Q ⊔ T := by
  rw [κ, commutatorHom_eq_one_iff, h.centralizer_eq t ht ht1]

theorem ker_κ (h : SingerSection Q T φ) {t : P} (ht : t ∈ T) (ht1 : t ≠ 1) :
    (h.κ t).ker = Q ⊔ T := by
  ext a
  exact h.κ_eq_one_iff ht ht1

theorem map_κ (h : SingerSection Q T φ) {t : P} (ht : t ∈ T) (x : X) (a : P) :
    φ x (h.κ t a) = h.κ t (φ x a) :=
  map_commutatorHom _ (φ x) (h.fixed x t ht) a

theorem mul_sq (h : SingerSection Q T φ) (a b : P) :
    (a * b) ^ 2 = b * a * b⁻¹ * a⁻¹ * a ^ 2 * b ^ 2 :=
  mul_sq_eq h.commutator_mem_center a b

theorem sq_mul_of_mem (h : SingerSection Q T φ) (g : P) {z : P} (hz : z ∈ Q) :
    (g * z) ^ 2 = g ^ 2 :=
  mul_sq_of_mem_center (h.le_center hz) (h.sq_eq_one z hz)

theorem card_sup_le (h : SingerSection Q T φ) :
    Nat.card (Q ⊔ T : Subgroup P) ≤ Nat.card Q * Nat.card T :=
  card_sup_le_of_le_center h.le_center

theorem map_comm (h : SingerSection Q T φ) (x y : X) (a : P) : φ x (φ y a) = φ y (φ x a) := by
  rw [← MulAut.mul_apply, ← map_mul, h.comm, map_mul, MulAut.mul_apply]

end SingerSection

end CFSG.ShultStronglyClosedTI.CentralSection
