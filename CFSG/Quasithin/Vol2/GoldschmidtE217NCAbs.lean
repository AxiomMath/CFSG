module

public import CFSG.Quasithin.Vol2.GoldschmidtE217L2Dih

public section

namespace CFSG.Quasithin

namespace E217R3

theorem mem_center_of_pow_three {S : Type*} [Group S] {y : S} {p : ℕ} (hp3 : ¬ 3 ∣ p)
    (h3 : y ^ 3 ∈ Subgroup.center S) (hp1 : y ^ p = 1) : y ∈ Subgroup.center S := by
  have hm : (y ^ 3) ^ (p / 3) ∈ Subgroup.center S := Subgroup.pow_mem _ h3 _
  have hr : y ^ (p % 3) = ((y ^ 3) ^ (p / 3))⁻¹ := by
    have h' : p % 3 + 3 * (p / 3) = p := by omega
    rw [eq_inv_iff_mul_eq_one, ← pow_mul, ← pow_add, h', hp1]
  have hr' : y ^ (p % 3) ∈ Subgroup.center S := hr ▸ Subgroup.inv_mem _ hm
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hmod with h | h
  · rwa [h, pow_one] at hr'
  · rw [h] at hr'
    have : y = y ^ 3 * (y ^ 2)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ hr')

theorem commute_of_prod_mem_center {S : Type*} [Group S] {u₀ u₁ : S} (hu₀ : u₀ * u₀ = 1)
    (hc : u₀ * u₁ ∈ Subgroup.center S) : u₀ * u₁ = u₁ * u₀ := by
  have h := Subgroup.mem_center_iff.1 hc u₀
  rw [← mul_assoc, hu₀, one_mul] at h
  calc u₀ * u₁ = u₀ * u₁ * (u₀ * u₀) := by rw [hu₀, mul_one]
    _ = u₀ * u₁ * u₀ * u₀ := by rw [← mul_assoc]
    _ = u₁ * u₀ := by rw [← h]

theorem not_oddCube_of_pair {S E : Type*} [Group S] [Group E] (θ : S →* E)
    (hker : θ.ker ≤ Subgroup.center S) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {u₀ u₁ : S}
    (hu₀ : u₀ * u₀ = 1) (hu₁ : u₁ * u₁ = 1) (hnc : u₀ * u₁ ≠ u₁ * u₀)
    (hconj : ∀ t s : E, orderOf t = 2 → orderOf s = 2 → ∃ g : E, t = g * s * g⁻¹)
    (hy : (u₀ * u₁) ^ p = 1) {z : E} (hz : orderOf z = 2) : ¬ OddCube z := by
  intro hO
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hyc : u₀ * u₁ ∉ Subgroup.center S := fun h => hnc (commute_of_prod_mem_center hu₀ h)
  have hθ0sq : θ u₀ * θ u₀ = 1 := by rw [← map_mul, hu₀, map_one]
  have hθ1sq : θ u₁ * θ u₁ = 1 := by rw [← map_mul, hu₁, map_one]
  have hpow : ∀ a : E, a * a = 1 → a ^ p = a := by
    intro a ha
    obtain ⟨m, hm⟩ := hpodd
    rw [hm, pow_succ, pow_mul, pow_two, ha, one_pow, one_mul]
  have hθy : (θ u₀ * θ u₁) ^ p = 1 := by rw [← map_mul, ← map_pow, hy, map_one]
  have hboth : θ u₀ = 1 → θ u₁ = 1 → False := fun h0 h1 =>
    hyc (hker (by rw [MonoidHom.mem_ker, map_mul, h0, h1, mul_one]))
  have hθ0 : θ u₀ ≠ 1 := fun h0 => by
    refine hboth h0 ?_
    rw [h0, one_mul] at hθy
    rwa [hpow _ hθ1sq] at hθy
  have hθ1 : θ u₁ ≠ 1 := fun h1 => by
    refine hboth ?_ h1
    rw [h1, mul_one] at hθy
    rwa [hpow _ hθ0sq] at hθy
  have hord0 : orderOf (θ u₀) = 2 := orderOf_eq_prime (by rwa [pow_two]) hθ0
  have hord1 : orderOf (θ u₁) = 2 := orderOf_eq_prime (by rwa [pow_two]) hθ1
  obtain ⟨k, hk⟩ := hconj (θ u₀) z hord0 hz
  obtain ⟨g, hg⟩ := hconj (θ u₁) (θ u₀) hord1 hord0
  have hO₀ : OddCube (θ u₀) := by
    rw [hk]
    exact hO.conj k
  have h1 : (θ u₀ * (g * θ u₀ * g⁻¹)) ^ p = 1 := by rw [← hg]; exact hθy
  have h3 := hO₀ g p hpodd h1
  rw [← hg, ← map_mul, ← map_pow] at h3
  have h3' : (u₀ * u₁) ^ 3 ∈ Subgroup.center S := hker h3
  refine hyc (mem_center_of_pow_three ?_ h3' hy)
  intro hdvd
  rcases (Nat.dvd_prime hp).1 hdvd with h | h <;> omega

theorem pow_eq_one_of_pow_three_eq_zero {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (hp3 : 3 ≤ p) {N : R} (hN : N ^ 3 = 0) : (1 + N) ^ p = 1 := by
  rw [add_pow_char_of_commute p (Commute.one_left N), one_pow]
  have : N ^ p = 0 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hp3
    rw [hk, pow_add, hN, zero_mul]
  rw [this, add_zero]

end E217R3

end CFSG.Quasithin
