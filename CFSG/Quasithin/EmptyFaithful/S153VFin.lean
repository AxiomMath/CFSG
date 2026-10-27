module

public import CFSG.Quasithin.EmptyFaithful.ModFA5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin.ModV

open Equiv CFSG.Quasithin.ModF CFSG.QuasithinUnique.A5.Delta5

@[expose] def zvec (p : Fin 5) : Fin 5 → ZMod 2 := fun i => if i = p then 0 else 1

theorem isEven_zvec : ∀ p : Fin 5, isEven (zvec p) := by
  unfold isEven zvec
  decide +kernel

theorem exists_fix_mapping : ∀ p q r : Fin 5, q ≠ p → r ≠ p →
    ∃ a : Perm (Fin 5), Perm.sign a = 1 ∧ a p = p ∧ a q = r := by
  decide +kernel

theorem fixes_of_normalizes : ∀ (p : Fin 5) (σ : Perm (Fin 5)), Perm.sign σ = 1 →
    (∀ τ : Perm (Fin 5), Perm.sign τ = 1 → τ p = p → (σ * τ * σ⁻¹) p = p) → σ p = p := by
  decide +kernel

theorem mem_klein_of_two_group : ∀ (p : Fin 5) (w : Perm (Fin 5)), w ^ 4 = 1 →
    (∀ γ : Perm (Fin 5), Perm.sign γ = 1 → γ p = p → (γ * w * γ⁻¹ * w⁻¹) ^ 4 = 1) → w ∈ klein p := by
  unfold klein
  decide +kernel

theorem exists_noFix : ∀ (p : Fin 5) (v : Perm (Fin 5)), v ∈ klein p → v ≠ 1 →
    ∃ (γ : Perm (Fin 5)) (w : Fin 5 → ZMod 2), Perm.sign γ = 1 ∧ γ p = p ∧ γ ^ 3 = 1 ∧ isEven w ∧
      pact v (w + pact γ w) ≠ w + pact γ w := by
  unfold klein
  decide +kernel

theorem exists_zvec : ∀ p : Fin 5, ∃ (γ₁ γ₂ : Perm (Fin 5)) (w₁ w₂ : Fin 5 → ZMod 2),
    Perm.sign γ₁ = 1 ∧ γ₁ p = p ∧ γ₁ ^ 3 = 1 ∧ isEven w₁ ∧
    Perm.sign γ₂ = 1 ∧ γ₂ p = p ∧ γ₂ ^ 3 = 1 ∧ isEven w₂ ∧
      (w₁ + pact γ₁ w₁) + (w₂ + pact γ₂ w₂) = zvec p := by
  intro p
  refine ⟨swap (p + 1) (p + 2) * swap (p + 2) (p + 3), swap (p + 3) (p + 4) * swap (p + 4) (p + 1),
    Pi.single (p + 1) 1 + Pi.single p 1, Pi.single (p + 3) 1 + Pi.single p 1, ?_⟩
  revert p
  unfold zvec isEven pact
  decide +kernel

theorem fix_klein : ∀ (p : Fin 5) (w : Fin 5 → ZMod 2), isEven w →
    (∀ v ∈ klein p, pact v w = w) → w = 0 ∨ w = zvec p := by
  unfold klein zvec isEven
  decide +kernel

theorem pow_four_of_two_power (w : Perm (Fin 5)) (h : ∃ n : ℕ, w ^ 2 ^ n = 1) : w ^ 4 = 1 := by
  obtain ⟨n, hn⟩ := h
  have h60 : ∀ w : Perm (Fin 5), w ^ 60 = 1 := by decide +kernel
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  have h2 : orderOf w ∣ 60 := orderOf_dvd_of_pow_eq_one (h60 w)
  rw [hj'] at h2
  have hj2 : j ≤ 2 := by
    by_contra hcon
    have h8 : 2 ^ 3 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := h8.trans h2
    omega
  have h4 : orderOf w ∣ 4 := by
    rw [hj']
    exact (pow_dvd_pow 2 hj2 : 2 ^ j ∣ 2 ^ 2)
  exact orderOf_dvd_iff_pow_eq_one.mp h4

theorem klein_eq_mul : ∀ (p : Fin 5) (v : Perm (Fin 5)), v ∈ klein p →
    ∃ c₁ c₂ : Perm (Fin 5), Perm.sign c₁ = 1 ∧ c₁ p = p ∧ c₁ ^ 3 = 1 ∧
      Perm.sign c₂ = 1 ∧ c₂ p = p ∧ c₂ ^ 3 = 1 ∧ v = c₁ * c₂ := by
  unfold klein
  decide +kernel

theorem pact_zvec : ∀ (p : Fin 5) (σ : Perm (Fin 5)), σ p = p → pact σ (zvec p) = zvec p := by
  unfold pact zvec
  decide +kernel

end CFSG.Quasithin.ModV
