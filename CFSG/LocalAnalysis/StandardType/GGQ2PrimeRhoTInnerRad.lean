module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTInnerGrp
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.GroupTheory.Perm.Sign

public section

namespace CFSG.GGQ2Prime

open Subgroup
open scoped commutatorElement

@[expose] def rhoTInnerRad {H Q B : Type*} [Group H] [Group Q] [Group B] (P : H →* Q)
    (R : B →* Q) (K : Subgroup B) : Subgroup B where
  carrier := {b | ∃ a₀ : H, P a₀ = R b ∧ ∀ a' : H, (∃ v ∈ K, P a' = R v) → a₀ * a' = a' * a₀}
  one_mem' := ⟨1, by simp, fun a' _ => by simp⟩
  mul_mem' := by
    rintro b₁ b₂ ⟨a₁, h₁, c₁⟩ ⟨a₂, h₂, c₂⟩
    refine ⟨a₁ * a₂, by rw [map_mul, map_mul, h₁, h₂], fun a' ha' => ?_⟩
    rw [mul_assoc, c₂ a' ha', ← mul_assoc, c₁ a' ha', mul_assoc]
  inv_mem' := by
    rintro b ⟨a₀, h, c⟩
    refine ⟨a₀⁻¹, by rw [map_inv, map_inv, h], fun a' ha' => ?_⟩
    have h1 := c a' ha'
    calc a₀⁻¹ * a' = a₀⁻¹ * (a' * a₀) * a₀⁻¹ := by group
      _ = a₀⁻¹ * (a₀ * a') * a₀⁻¹ := by rw [h1]
      _ = a' * a₀⁻¹ := by group

theorem rhoTInner_reflection_mem_rad {H Q B : Type*} [Group H] [Group Q] [Group B] [Finite B]
    [IsMulCommutative B] (P : H →* Q) (hcen : ∀ z, P z = 1 → z ∈ center H) (R : B →* Q)
    (hB3 : ∀ b : B, b ^ 3 = 1) (hcube : ∀ (a : H) (b : B), P a = R b → a ^ 3 = 1)
    (K : Subgroup B) (hlift : ∀ b ∈ K, ∃ a : H, P a = R b) {φ : MulAut B}
    (hφ2 : ∀ b, φ (φ b) = b) (hφcard : Nat.card {b : B // φ b = b} * 3 = Nat.card B) {s : H}
    (hs : ∀ (a : H) (b : B), P a = R b → P (s * a * s⁻¹) = R (φ b))
    (hdK : ∀ b : B, φ b * b⁻¹ ∈ K) (b : B) : φ b * b⁻¹ ∈ rhoTInnerRad P R K := by
  obtain ⟨a₀, ha₀⟩ := hlift _ (hdK b)
  refine ⟨a₀, ha₀, fun a' ⟨v, _, hv⟩ => ?_⟩
  set d := φ b * b⁻¹ with hd
  by_cases hd1 : d = 1
  · have h1 : P a₀ = 1 := by rw [ha₀, hd1, map_one]
    exact (mem_center_iff.1 (hcen a₀ h1) a').symm
  · have hφd : φ d = d⁻¹ := by
      rw [hd, map_mul, map_inv, hφ2 b, mul_inv_rev, inv_inv]
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (rhoTInner_mem_zpowers_of_reflection hB3 hφcard b v hd1)
    have hφv : φ v = v * d ^ j := by rw [hj, mul_comm' v, inv_mul_cancel_right]
    have hPz₁ : P (a₀ * (s * a₀ * s⁻¹)) = 1 := by
      rw [map_mul, hs a₀ d ha₀, hφd, ha₀, map_inv]; exact mul_inv_cancel _
    have h₁ : s * a₀ * s⁻¹ = a₀⁻¹ * (a₀ * (s * a₀ * s⁻¹)) := by group
    have hPz₂ : P ((a' * a₀ ^ j)⁻¹ * (s * a' * s⁻¹)) = 1 := by
      have e1 : P (a' * a₀ ^ j) = R (v * d ^ j) := by
        rw [map_mul P a' (a₀ ^ j), map_zpow P a₀ j, hv, ha₀, map_mul R v (d ^ j),
          map_zpow R d j]
      rw [map_mul, map_inv, e1, hs a' v hv, hφv]
      exact inv_mul_cancel _
    have h₂ : s * a' * s⁻¹ = a' * a₀ ^ j * ((a' * a₀ ^ j)⁻¹ * (s * a' * s⁻¹)) := by group
    have hc : ⁅a₀, a'⁆ ∈ center H := by
      refine hcen _ ?_
      rw [map_commutatorElement, ha₀, hv, ← map_commutatorElement]
      rw [commutatorElement_eq_one_iff_mul_comm.2 (mul_comm' d v), map_one]
    exact rhoTInner_comm_of_conj (hcen _ hPz₁) (hcen _ hPz₂) hc (hcube a₀ d ha₀) h₁ h₂

theorem rhoTInner_mem_of_swaps {B : Type*} [Group B] (D : Subgroup B) {α : Type*}
    [DecidableEq α] [Finite α] (E : Equiv.Perm α →* MulAut B)
    (hsw : ∀ x y : α, x ≠ y → ∀ b : B, E (Equiv.swap x y) b * b⁻¹ ∈ D)
    (σ : Equiv.Perm α) (b : B) : E σ b * b⁻¹ ∈ D := by
  let Sg : Subgroup (MulAut B) :=
    { carrier := {φ | ∀ b : B, φ b * b⁻¹ ∈ D}
      one_mem' := fun b => by simp
      mul_mem' := fun {φ ψ} hφ hψ b => by
        rw [MulAut.mul_apply]
        have h := D.mul_mem (hφ (ψ b)) (hψ b)
        rwa [mul_assoc, inv_mul_cancel_left] at h
      inv_mem' := fun {φ} hφ b => by
        have h := D.inv_mem (hφ (φ⁻¹ b))
        simpa [MulAut.apply_inv_self, mul_inv_rev] using h }
  have hS : closure {σ : Equiv.Perm α | σ.IsSwap} ≤ Sg.comap E := by
    rw [closure_le]
    rintro _ ⟨x, y, hxy, rfl⟩
    exact hsw x y hxy
  rw [Equiv.Perm.closure_isSwap] at hS
  exact hS (mem_top σ) b

theorem rhoTInner_commute_of_rad {H Q B : Type*} [Group H] [Group Q] [Group B] (P : H →* Q)
    (hcen : ∀ z, P z = 1 → z ∈ center H) (R : B →* Q) (K : Subgroup B)
    (χ : B →* Multiplicative (ZMod 3)) (hχ : ∀ b, χ b = 1 → b ∈ rhoTInnerRad P R K)
    {a a' : H} {b b' : B} (hb : b ∈ K) (hb' : b' ∈ K) (ha : P a = R b) (ha' : P a' = R b') :
    a * a' = a' * a := by
  have key : ∀ (c : B) (u : H), χ c = 1 → P u = R c →
      ∀ a'' : H, (∃ v ∈ K, P a'' = R v) → u * a'' = a'' * u := by
    intro c u hc hu a'' ha''
    obtain ⟨a₀, h₀, hcomm⟩ := hχ c hc
    have hz : P (a₀⁻¹ * u) = 1 := by rw [map_mul, map_inv, h₀, hu, inv_mul_cancel]
    have hu' : u = a₀ * (a₀⁻¹ * u) := by group
    rw [hu', mul_assoc, (mem_center_iff.1 (hcen _ hz) a'').symm, ← mul_assoc, hcomm a'' ha'',
      mul_assoc]
  by_cases hχb : χ b = 1
  · exact key b a hχb ha a' ⟨b', hb', ha'⟩
  by_cases hχb' : χ b' = 1
  · exact (key b' a' hχb' ha' a ⟨b, hb, ha⟩).symm
  have hgen : ∀ u w : Multiplicative (ZMod 3), u ≠ 1 → ∃ t : Fin 3, w = u ^ (t : ℕ) := by decide
  obtain ⟨t, ht⟩ := hgen (χ b) (χ b') hχb
  have hcK : b' * (b ^ (t : ℕ))⁻¹ ∈ K := K.mul_mem hb' (K.inv_mem (K.pow_mem hb _))
  have hχc : χ (b' * (b ^ (t : ℕ))⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, ← ht, mul_inv_cancel]
  have hPu : P (a' * (a ^ (t : ℕ))⁻¹) = R (b' * (b ^ (t : ℕ))⁻¹) := by
    rw [map_mul, map_inv, map_pow, ha, ha', map_mul, map_inv, map_pow]
  have hu := key _ _ hχc hPu a ⟨b, hb, ha⟩
  have ha'eq : a' = a' * (a ^ (t : ℕ))⁻¹ * a ^ (t : ℕ) := by group
  rw [ha'eq]
  calc a * (a' * (a ^ (t : ℕ))⁻¹ * a ^ (t : ℕ))
      = a * (a' * (a ^ (t : ℕ))⁻¹) * a ^ (t : ℕ) := by rw [mul_assoc a]
    _ = a' * (a ^ (t : ℕ))⁻¹ * a * a ^ (t : ℕ) := by rw [← hu]
    _ = a' * (a ^ (t : ℕ))⁻¹ * (a ^ (t : ℕ) * a) := by rw [mul_assoc _ a, ← pow_succ, pow_succ']
    _ = a' * (a ^ (t : ℕ))⁻¹ * a ^ (t : ℕ) * a := by rw [← mul_assoc]

end CFSG.GGQ2Prime
