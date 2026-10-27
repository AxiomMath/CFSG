module

public import CFSG.Walter.ReeOrder.Ward.LTable

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

structure WardSetup (G : Type) [Group G] [Fintype G] (L : Type) [Group L] [Fintype L] (q : ℕ)
    (e : ℤ) (IV : Bool := true) where
  W : WardL L q e
  q_ge : 27 ≤ q
  q_pow : ∃ p f : ℕ, p.Prime ∧ q = p ^ f
  J : G
  J_mul : J * J = 1
  J_ne : J ≠ 1
  κ : L →* G
  κ_inj : Function.Injective κ
  κ_comm : ∀ y, κ y * J = J * κ y
  J_not_mem : ∀ y, κ y ≠ J
  centralizer : ∀ g : G, g * J = J * g → ∃ y, g = κ y ∨ g = J * κ y
  involution_conj : ∀ x : G, orderOf x = 2 → IsConj x J
  normalizer : IV = true → ∀ r ∈ W.Ro, r ≠ 1 → ∀ b : G,
    b⁻¹ * κ r * b ∈ Subgroup.zpowers (κ r) → b * J = J * b
  A : G
  orderOf_A : orderOf A = 3
  A_J : A⁻¹ * J * A = κ W.J'
  A_J' : A⁻¹ * κ W.J' * A = J * κ W.J'
  A_So : ∀ ρ ∈ W.So, ∃ ρ' ∈ W.So, A⁻¹ * κ ρ * A = κ ρ'
  A_not_comm : ∃ ρ ∈ W.So, A * κ ρ ≠ κ ρ * A

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

theorem J_inv : S.J⁻¹ = S.J := inv_eq_of_mul_eq_one_right S.J_mul

theorem orderOf_J : orderOf S.J = 2 :=
  orderOf_eq_prime (by rw [sq, S.J_mul]) S.J_ne

theorem κ_comm' (y : L) : S.J * S.κ y = S.κ y * S.J := (S.κ_comm y).symm

theorem J_mul_ne (y z : L) : S.J * S.κ y ≠ S.κ z := by
  intro h
  apply S.J_not_mem (z * y⁻¹)
  rw [map_mul, map_inv, ← h, mul_assoc, mul_inv_cancel, mul_one]

theorem κ_eq_iff (y z : L) : S.κ y = S.κ z ↔ y = z := S.κ_inj.eq_iff

theorem J_κ_eq_iff (y z : L) : S.J * S.κ y = S.J * S.κ z ↔ y = z := by
  rw [mul_right_inj, S.κ_eq_iff]

theorem κ_mem_centralizer (y : L) : S.κ y ∈ Subgroup.centralizer ({S.J} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact S.κ_comm y

theorem J_mem_centralizer : S.J ∈ Subgroup.centralizer ({S.J} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]

theorem mem_centralizer_iff (g : G) :
    g ∈ Subgroup.centralizer ({S.J} : Set G) ↔ ∃ y, g = S.κ y ∨ g = S.J * S.κ y := by
  constructor
  · intro hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact S.centralizer g hg
  · rintro ⟨y, rfl | rfl⟩
    · exact S.κ_mem_centralizer y
    · exact Subgroup.mul_mem _ S.J_mem_centralizer (S.κ_mem_centralizer y)

theorem odd_mem_κ {g : G} (hg : g * S.J = S.J * g) (hodd : Odd (orderOf g)) :
    ∃ y, g = S.κ y := by
  obtain ⟨y, rfl | rfl⟩ := S.centralizer g hg
  · exact ⟨y, rfl⟩
  · exfalso
    obtain ⟨k, hk⟩ := hodd
    have hpow : (S.J * S.κ y) ^ (2 * k + 1) = 1 := by rw [← hk, pow_orderOf_eq_one]
    have hcomm : Commute S.J (S.κ y) := S.κ_comm' y
    rw [hcomm.mul_pow, pow_succ, pow_mul, sq, S.J_mul, one_pow, one_mul] at hpow
    have h2 : S.J * S.κ (y ^ (2 * k + 1)) = 1 := by
      rw [map_pow]
      exact hpow
    apply S.J_mul_ne (y ^ (2 * k + 1)) 1
    rw [h2, map_one]

end WardSetup

end CFSG.Walter.Ward
