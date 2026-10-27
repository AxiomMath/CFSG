module

public import CFSG.Quasithin.EmptyFaithful.S153E55D

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise MatrixGroups

namespace S153E56e

section Core

variable {A : Type*} [Group A]

theorem s3_inv : ∀ α γ : Equiv.Perm (Fin 3), α * α = 1 → α ≠ 1 → γ * γ * γ = 1 → γ ≠ 1 →
    α * γ⁻¹ * α⁻¹ = γ := by decide +kernel

theorem perm3_pow_six : ∀ x : Equiv.Perm (Fin 3), x ^ 6 = 1 := by decide +kernel

theorem sq_eq_one_of_pow {α : Type*} [Group α] (h6 : ∀ x : α, x ^ 6 = 1) {x : α} {k : ℕ}
    (h : x ^ 2 ^ k = 1) : x * x = 1 := by
  cases k with
  | zero =>
    rw [pow_zero, pow_one] at h
    rw [h, mul_one]
  | succ k =>
    have h1 : (x ^ 2) ^ 2 ^ k = 1 := by rw [← pow_mul, ← pow_succ']; exact h
    have h2 : (x ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact h6 x
    have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
    have hg : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [hg, pow_one] at h3
    rw [← pow_two]
    exact h3

theorem eq_one_of_sq_two_pow {c : A} (hc3 : c ^ 3 = 1) {k : ℕ} (h : (c * c) ^ 2 ^ k = 1) : c = 1 := by
  have h1 : c ^ 2 ^ (k + 1) = 1 := by rw [pow_succ', pow_mul, pow_two]; exact h
  have h2 := pow_gcd_eq_one.2 ⟨h1, hc3⟩
  have hg : Nat.gcd (2 ^ (k + 1)) 3 = 1 := Nat.Coprime.pow_left (k + 1) (by norm_num)
  rw [hg, pow_one] at h2
  exact h2

theorem inv_action {N₁ : Subgroup A} (e : ↥N₁ ≃* Equiv.Perm (Fin 3)) {c a : A} (hc : c ∈ N₁)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (ha : a ∈ N₁) (haa : a * a = 1) (ha1 : a ≠ 1) :
    a * c⁻¹ * a⁻¹ = c := by
  have hi : ∀ x : ↥N₁, e x = 1 ↔ x = 1 := fun x => map_eq_one_iff e e.injective
  have hα2 : e ⟨a, ha⟩ * e ⟨a, ha⟩ = 1 := by
    rw [← map_mul, (hi _).2 (Subtype.ext haa)]
  have hα1 : e ⟨a, ha⟩ ≠ 1 := fun h => ha1 (congrArg Subtype.val ((hi _).1 h))
  have hγ3 : e ⟨c, hc⟩ * e ⟨c, hc⟩ * e ⟨c, hc⟩ = 1 := by
    rw [← map_mul, ← map_mul, (hi _).2 (Subtype.ext (by simpa [pow_succ, mul_assoc] using hc3))]
  have hγ1 : e ⟨c, hc⟩ ≠ 1 := fun h => hc1 (congrArg Subtype.val ((hi _).1 h))
  have key := s3_inv _ _ hα2 hα1 hγ3 hγ1
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul] at key
  have := congrArg Subtype.val (e.injective key)
  simpa using this

theorem core_conj {N₁ N₂ : Subgroup A} (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hinf : N₁ ⊓ N₂ = ⊥) (e : ↥N₁ ≃* Equiv.Perm (Fin 3)) {c a b : A} (hc : c ∈ N₁) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) (ha : a ∈ N₁) (hb : b ∈ N₂) (ha1 : a ≠ 1) (hab : (a * b) * (a * b) = 1) :
    (a * b) * (c⁻¹ * (a * b) * c) = c * c := by
  have hb' : ∀ x ∈ N₁, b * x = x * b := fun x hx => (hcomm x hx b hb).symm
  have hab' : a * b = b * a := hcomm a ha b hb
  have h1 : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hab']
      _ = (a * b) * (a * b) := by group
      _ = 1 := hab
  have haa : a * a = 1 := by
    have h2 : a * a ∈ N₁ ⊓ N₂ := by
      refine ⟨N₁.mul_mem ha ha, ?_⟩
      have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact N₂.inv_mem (N₂.mul_mem hb hb)
    rw [hinf, Subgroup.mem_bot] at h2
    exact h2
  have hbb : b * b = 1 := by
    rw [haa, one_mul] at h1
    exact h1
  have hs3 := inv_action e hc hc3 hc1 ha haa ha1
  calc (a * b) * (c⁻¹ * (a * b) * c) = a * (b * c⁻¹) * a * b * c := by group
    _ = a * (c⁻¹ * b) * a * b * c := by rw [hb' c⁻¹ (N₁.inv_mem hc)]
    _ = a * c⁻¹ * (b * a) * b * c := by group
    _ = a * c⁻¹ * (a * b) * b * c := by rw [hb' a ha]
    _ = a * c⁻¹ * a * (b * b) * c := by group
    _ = a * c⁻¹ * a * c := by rw [hbb, mul_one]
    _ = (a * c⁻¹ * a⁻¹) * (a * a) * c := by group
    _ = c * c := by rw [hs3, haa, mul_one]

theorem core_comm {N₁ N₂ : Subgroup A} (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hinf : N₁ ⊓ N₂ = ⊥) (e : ↥N₁ ≃* Equiv.Perm (Fin 3)) {c : A} (hc : c ∈ N₁) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) {ρ : A} (hρ : ρ ∈ N₁ ⊔ N₂) {k k' : ℕ} (hk : ρ ^ 2 ^ k = 1)
    (hk' : (c * ρ * c⁻¹ * ρ⁻¹) ^ 2 ^ k' = 1) : c * ρ * c⁻¹ * ρ⁻¹ = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := S153E55.mem_sup_of_comm hcomm hρ
  have hb' : ∀ x ∈ N₁, b * x = x * b := fun x hx => (hcomm x hx b hb).symm
  have hak : a ^ 2 ^ k = 1 := by
    have hcm : Commute a b := hcomm a ha b hb
    have h1 : (a * b) ^ 2 ^ k = a ^ 2 ^ k * b ^ 2 ^ k := hcm.mul_pow _
    rw [h1] at hk
    have h2 : a ^ 2 ^ k ∈ N₁ ⊓ N₂ := by
      refine ⟨N₁.pow_mem ha _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hk]
      exact N₂.inv_mem (N₂.pow_mem hb _)
    rw [hinf, Subgroup.mem_bot] at h2
    exact h2
  have haa : a * a = 1 := by
    have h1 : (e ⟨a, ha⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨a, ha⟩ : ↥N₁) ^ 2 ^ k = 1 := Subtype.ext hak
      rw [this, map_one]
    have h2 := sq_eq_one_of_pow perm3_pow_six h1
    rw [← map_mul] at h2
    have h3 := e.injective (h2.trans (map_one e).symm)
    simpa using congrArg Subtype.val h3
  by_cases ha1 : a = 1
  · rw [ha1, one_mul]
    have := hb' c hc
    calc c * b * c⁻¹ * b⁻¹ = (c * b) * (b * c)⁻¹ := by group
      _ = 1 := by rw [← this]; group
  · exfalso
    have hs3 := inv_action e hc hc3 hc1 ha haa ha1
    have hform : c * (a * b) * c⁻¹ * (a * b)⁻¹ = c * c := by
      calc c * (a * b) * c⁻¹ * (a * b)⁻¹ = c * a * (b * c⁻¹) * b⁻¹ * a⁻¹ := by group
        _ = c * a * (c⁻¹ * b) * b⁻¹ * a⁻¹ := by rw [hb' c⁻¹ (N₁.inv_mem hc)]
        _ = c * (a * c⁻¹ * a⁻¹) := by group
        _ = c * c := by rw [hs3]
    rw [hform] at hk'
    exact hc1 (eq_one_of_sq_two_pow hc3 hk')

end Core

end S153E56e

end CFSG.Quasithin
