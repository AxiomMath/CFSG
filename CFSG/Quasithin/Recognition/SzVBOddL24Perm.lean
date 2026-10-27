module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Quasithin.SzVB

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem perm_core_fin :
    ∀ m τ : Equiv.Perm (Fin 5), m * m = 1 → m ≠ 1 → m 0 = 0 → τ 0 = 0 → τ ≠ 1 →
      τ * τ * τ = 1 →
      ∃ U : Fin 5, m U ≠ U ∧ (τ * m * τ⁻¹) U ≠ U ∧ m U ≠ (τ * m * τ⁻¹) U := by
  decide +kernel

theorem perm_core {Ω : Type*} [Finite Ω] (hΩ : Nat.card Ω = 5) (ω : Ω) (m τ : Equiv.Perm Ω)
    (hm2 : m * m = 1) (hm1 : m ≠ 1) (hmω : m ω = ω) (hτω : τ ω = ω) (hτ1 : τ ≠ 1)
    (hτ3 : τ * τ * τ = 1) :
    ∃ U : Ω, m U ≠ U ∧ (τ * m * τ⁻¹) U ≠ U ∧ m U ≠ (τ * m * τ⁻¹) U := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  have hc : Fintype.card Ω = 5 := by rw [← Nat.card_eq_fintype_card]; exact hΩ
  let e₀ : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hc
  let e : Ω ≃ Fin 5 := e₀.trans (Equiv.swap (e₀ ω) 0)
  have he : e ω = 0 := by simp [e]
  let φ : Equiv.Perm Ω ≃* Equiv.Perm (Fin 5) := e.permCongrHom
  have hφ : ∀ (p : Equiv.Perm Ω) (x : Ω), φ p (e x) = e (p x) := by
    intro p x
    simp [φ, Equiv.permCongr_apply]
  obtain ⟨U, h1, h2, h3⟩ := perm_core_fin (φ m) (φ τ) (by rw [← map_mul, hm2, map_one])
    (fun h => hm1 (φ.injective (by rw [h, map_one]))) (by rw [← he, hφ, hmω])
    (by rw [← he, hφ, hτω]) (fun h => hτ1 (φ.injective (by rw [h, map_one])))
    (by rw [← map_mul, ← map_mul, hτ3, map_one])
  obtain ⟨x, rfl⟩ := e.surjective U
  have hconj : φ τ * φ m * (φ τ)⁻¹ = φ (τ * m * τ⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [hconj, hφ] at h2 h3
  rw [hφ] at h1 h3
  refine ⟨x, fun h => h1 (by rw [h]), fun h => h2 (by rw [h]), fun h => h3 (by rw [h])⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem perm_exists_fixed_fin :
    ∀ τ : Equiv.Perm (Fin 5), τ ≠ 1 → τ * τ * τ = 1 → τ 0 = 0 → ∃ μ : Fin 5, μ ≠ 0 ∧ τ μ = μ := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem perm_cube_or_even_fin :
    ∀ σ : Equiv.Perm (Fin 5), σ 0 = 0 → σ ^ 3 = 1 ∨ σ ^ 2 = 1 ∨ σ ^ 4 = 1 := by
  decide +kernel

theorem perm_exists_fixed {Ω : Type*} [Finite Ω] (hΩ : Nat.card Ω = 5) (ω : Ω)
    (τ : Equiv.Perm Ω) (hτ1 : τ ≠ 1) (hτ3 : τ * τ * τ = 1) (hτω : τ ω = ω) :
    ∃ μ : Ω, μ ≠ ω ∧ τ μ = μ := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  have hc : Fintype.card Ω = 5 := by rw [← Nat.card_eq_fintype_card]; exact hΩ
  let e₀ : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hc
  let e : Ω ≃ Fin 5 := e₀.trans (Equiv.swap (e₀ ω) 0)
  have he : e ω = 0 := by simp [e]
  let φ : Equiv.Perm Ω ≃* Equiv.Perm (Fin 5) := e.permCongrHom
  have hφ : ∀ (p : Equiv.Perm Ω) (x : Ω), φ p (e x) = e (p x) := by
    intro p x
    simp [φ, Equiv.permCongr_apply]
  obtain ⟨μ, hμ0, hμ⟩ := perm_exists_fixed_fin (φ τ)
    (fun h => hτ1 (φ.injective (by rw [h, map_one])))
    (by rw [← map_mul, ← map_mul, hτ3, map_one]) (by rw [← he, hφ, hτω])
  obtain ⟨x, rfl⟩ := e.surjective μ
  rw [hφ] at hμ
  refine ⟨x, fun h => hμ0 (by rw [h, he]), e.injective hμ⟩

theorem perm_cube_of_odd {Ω : Type*} [Finite Ω] (hΩ : Nat.card Ω = 5) (ω : Ω)
    (σ : Equiv.Perm Ω) (hσω : σ ω = ω) (hodd : Odd (orderOf σ)) : σ ^ 3 = 1 := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  have hc : Fintype.card Ω = 5 := by rw [← Nat.card_eq_fintype_card]; exact hΩ
  let e₀ : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hc
  let e : Ω ≃ Fin 5 := e₀.trans (Equiv.swap (e₀ ω) 0)
  have he : e ω = 0 := by simp [e]
  let φ : Equiv.Perm Ω ≃* Equiv.Perm (Fin 5) := e.permCongrHom
  have hφ : ∀ (p : Equiv.Perm Ω) (x : Ω), φ p (e x) = e (p x) := by
    intro p x
    simp [φ, Equiv.permCongr_apply]
  have key : ∀ j : ℕ, σ ^ (2 ^ j) = 1 → σ = 1 := by
    intro j hj
    have hd : orderOf σ ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
    have hc : Nat.Coprime (orderOf σ) (2 ^ j) := (Odd.coprime_two_right hodd).pow_right j
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc hd)
  rcases perm_cube_or_even_fin (φ σ) (by rw [← he, hφ, hσω]) with h | h | h
  · exact φ.injective (by rw [map_pow, h, map_one])
  · have h2 : σ ^ 2 = 1 := φ.injective (by rw [map_pow, h, map_one])
    rw [key 1 (by simpa using h2)]
    simp
  · have h4 : σ ^ 4 = 1 := φ.injective (by rw [map_pow, h, map_one])
    rw [key 2 (by simpa using h4)]
    simp

end CFSG.Quasithin.SzVB
