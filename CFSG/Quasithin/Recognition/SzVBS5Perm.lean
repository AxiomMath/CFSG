module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Quasithin.SzVB

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem perm_s5_fin :
    ∀ m τ : Equiv.Perm (Fin 5), m 0 = 0 → m 1 = 1 → τ 0 = 0 → τ 1 = 1 → τ ≠ 1 →
      τ * τ * τ = 1 → m ≠ 1 →
      m * m * m = 1 ∨
        (m * (τ * m * τ⁻¹) ≠ 1 ∧
          m * (τ * m * τ⁻¹) * (m * (τ * m * τ⁻¹)) * (m * (τ * m * τ⁻¹)) = 1) := by
  decide +kernel

theorem perm_s5 {Ω : Type*} [Finite Ω] (hΩ : Nat.card Ω = 5) {ω μ : Ω} (hμ : μ ≠ ω)
    (m τ : Equiv.Perm Ω) (hmω : m ω = ω) (hmμ : m μ = μ) (hτω : τ ω = ω) (hτμ : τ μ = μ)
    (hτ1 : τ ≠ 1) (hτ3 : τ * τ * τ = 1) (hm1 : m ≠ 1) :
    m * m * m = 1 ∨
      (m * (τ * m * τ⁻¹) ≠ 1 ∧
        m * (τ * m * τ⁻¹) * (m * (τ * m * τ⁻¹)) * (m * (τ * m * τ⁻¹)) = 1) := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  have hc : Fintype.card Ω = 5 := by rw [← Nat.card_eq_fintype_card]; exact hΩ
  let e₀ : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hc
  let e₁ : Ω ≃ Fin 5 := e₀.trans (Equiv.swap (e₀ ω) 0)
  have he₁ω : e₁ ω = 0 := by simp [e₁]
  have he₁μ : e₁ μ ≠ 0 := fun h => hμ (e₁.injective (h.trans he₁ω.symm))
  let e : Ω ≃ Fin 5 := e₁.trans (Equiv.swap (e₁ μ) 1)
  have heω : e ω = 0 := by
    simp only [e, Equiv.trans_apply, he₁ω]
    exact Equiv.swap_apply_of_ne_of_ne he₁μ.symm (by decide)
  have heμ : e μ = 1 := by simp [e]
  let φ : Equiv.Perm Ω ≃* Equiv.Perm (Fin 5) := e.permCongrHom
  have hφ : ∀ (p : Equiv.Perm Ω) (x : Ω), φ p (e x) = e (p x) := by
    intro p x
    simp [φ, Equiv.permCongr_apply]
  have hne1 : ∀ p : Equiv.Perm Ω, p ≠ 1 → φ p ≠ 1 := fun p hp h =>
    hp (φ.injective (by rw [h, map_one]))
  have hconj : φ (m * (τ * m * τ⁻¹)) = φ m * (φ τ * φ m * (φ τ)⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv]
  rcases perm_s5_fin (φ m) (φ τ) (by rw [← heω, hφ, hmω]) (by rw [← heμ, hφ, hmμ])
      (by rw [← heω, hφ, hτω]) (by rw [← heμ, hφ, hτμ]) (hne1 τ hτ1)
      (by rw [← map_mul, ← map_mul, hτ3, map_one]) (hne1 m hm1) with h | ⟨h1, h2⟩
  · left
    refine φ.injective ?_
    rw [map_mul, map_mul, map_one]
    exact h
  · right
    refine ⟨fun h => h1 ?_, φ.injective ?_⟩
    · rw [← hconj, h, map_one]
    · rw [← hconj, ← map_mul, ← map_mul] at h2
      rw [h2, map_one]

theorem eq_one_of_cube_of_two_pow {H : Type*} [Group H] {z : H} {k : ℕ} (h3 : z * z * z = 1)
    (h2 : z ^ 2 ^ k = 1) : z = 1 := by
  have hd3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [pow_three']; exact h3)
  have hd2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have hc : Nat.Coprime (orderOf z) (2 ^ k) :=
    Nat.Coprime.coprime_dvd_left hd3 (Nat.Coprime.pow_right k (by decide))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc hd2)

end CFSG.Quasithin.SzVB
