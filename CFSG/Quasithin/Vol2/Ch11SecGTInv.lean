module

public import CFSG.Quasithin.Vol2.Ch11SecGTransv

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open

variable {G : Type} [Group G]

theorem inv_pow_mem_centralizer {Y : Subgroup G} {a x : G}
    (hx : x ∈ Subgroup.normalizer (Y : Set G))
    (hinv : a * x * a⁻¹ * x ∈ Subgroup.centralizer (Y : Set G)) (k : ℕ) :
    a * x ^ k * a⁻¹ * x ^ k ∈ Subgroup.centralizer (Y : Set G) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := conj_mem_centralizer (inv_mem (pow_mem hx k)) hinv
    have e : a * x ^ (k + 1) * a⁻¹ * x ^ (k + 1) = (a * x ^ k * a⁻¹ * x ^ k) *
        ((x ^ k)⁻¹ * (a * x * a⁻¹ * x) * ((x ^ k)⁻¹)⁻¹) := by
      rw [pow_succ]
      group
    rw [e]
    exact mul_mem ih h1

theorem inv_inv_mem_centralizer {Y : Subgroup G} {a w : G}
    (hw : w ∈ Subgroup.normalizer (Y : Set G))
    (hinv : a * w * a⁻¹ * w ∈ Subgroup.centralizer (Y : Set G)) :
    a * w⁻¹ * a⁻¹ * w⁻¹ ∈ Subgroup.centralizer (Y : Set G) := by
  have h1 := conj_mem_centralizer hw hinv
  have e : a * w⁻¹ * a⁻¹ * w⁻¹ = (w * (a * w * a⁻¹ * w) * w⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h1

theorem inv_mem_centralizer_commutator' {Y : Subgroup G} {a z : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) (hz : z ∈ Subgroup.normalizer (Y : Set G))
    (ha2 : a ^ 2 ∈ Subgroup.centralizer (Y : Set G)) :
    a * (a * z * a⁻¹ * z⁻¹) * a⁻¹ * (a * z * a⁻¹ * z⁻¹) ∈
      Subgroup.centralizer (Y : Set G) := by
  have hw : z * a * z⁻¹ * a⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    mul_mem (mul_mem (mul_mem hz ha) (inv_mem hz)) (inv_mem ha)
  have h := inv_inv_mem_centralizer hw (inv_mem_centralizer_commutator ha hz ha2)
  have e : a * z * a⁻¹ * z⁻¹ = (z * a * z⁻¹ * a⁻¹)⁻¹ := by group
  rw [e]
  exact h

theorem mem_centralizer_of_inv_of_primes {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {a y₀ : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) (hy₀ : y₀ ∈ Y)
    (htr : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = y₀) {m : ℕ} (hm : 0 < m)
    (hprimes : ∀ r : ℕ, r.Prime → r ∣ m → 5 ≤ r) {x : G}
    (hx : x ∈ Subgroup.normalizer (Y : Set G)) (hxm : x ^ m ∈ Subgroup.centralizer (Y : Set G))
    (hinv : a * x * a⁻¹ * x ∈ Subgroup.centralizer (Y : Set G)) :
    x ∈ Subgroup.centralizer (Y : Set G) := by
  induction m using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    by_cases h1 : m = 1
    · rw [h1, pow_one] at hxm
      exact hxm
    obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨m', rfl⟩ := hrm
    have hm' : 0 < m' := Nat.pos_of_mul_pos_left hm
    have hu : x ^ m' ∈ Subgroup.centralizer (Y : Set G) := by
      refine mem_centralizer_of_inv hY ha (pow_mem hx m') hy₀ htr hr (hprimes r hr
        (dvd_mul_right r m')) ?_ (inv_pow_mem_centralizer hx hinv m')
      rwa [← pow_mul, mul_comm]
    have hlt : m' < r * m' := by
      have := hr.two_le
      nlinarith
    exact ih m' hlt hm' (fun s hs hsm => hprimes s hs (dvd_mul_of_dvd_right hsm r)) hx hu hinv

theorem exists_two_pow_mem_centralizer {Y : Subgroup G} (hY : IsElemAbelian 2 Y) {a y₀ : G}
    (ha : a ∈ Subgroup.normalizer (Y : Set G)) (hy₀ : y₀ ∈ Y)
    (htr : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = y₀) {m : ℕ} (hm : 0 < m)
    (hprimes : ∀ r : ℕ, r.Prime → r ∣ m → 5 ≤ r) {O : Subgroup G} (hO : IsPGroup 2 O) {x : G}
    (hx : x ∈ Subgroup.normalizer (Y : Set G)) (hxm : x ^ m ∈ O)
    (hinv : a * x * a⁻¹ * x ∈ Subgroup.centralizer (Y : Set G)) :
    ∃ e : ℕ, x ^ 2 ^ e ∈ Subgroup.centralizer (Y : Set G) := by
  obtain ⟨e, he⟩ := hO ⟨x ^ m, hxm⟩
  have he' : (x ^ m) ^ 2 ^ e = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  refine ⟨e, mem_centralizer_of_inv_of_primes hY ha hy₀ htr hm hprimes (pow_mem hx _) ?_
    (inv_pow_mem_centralizer hx hinv _)⟩
  rw [← pow_mul, mul_comm, pow_mul, he']
  exact one_mem _

end CFSG.Quasithin.Vol2.Ch11.SecG
