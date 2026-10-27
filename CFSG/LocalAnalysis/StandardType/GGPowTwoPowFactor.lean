module

public import CFSG.Assembly.Defs
public import Mathlib.Algebra.Group.Commutator

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement Pointwise

theorem exists_mul_of_pow_two_pow_mem {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E N U : Subgroup X} (hE : IsElemAbelian p E) (hEN : E ≤ Subgroup.normalizer (N : Set X))
    (hUH : U ≤ E ⊔ N) {h : X} (hh : h ∈ E ⊔ N) {k : ℕ} (hk : h ^ (2 ^ k) ∈ U) :
    ∃ n ∈ N, ∃ u ∈ U, h = n * u := by
  have hMN : E ⊔ N ≤ Subgroup.normalizer (N : Set X) :=
    sup_le hEN Subgroup.le_normalizer
  have hconj : ∀ e ∈ E, ∀ m ∈ N, e⁻¹ * m * e ∈ N := by
    intro e he m hm
    exact (Subgroup.mem_normalizer_iff''.mp (hEN he) m).mp hm
  have key : ∀ e ∈ E, ∀ n ∈ N, ∀ i : ℕ, ∃ m ∈ N, (e * n) ^ i = e ^ i * m := by
    intro e he n hn i
    induction i with
    | zero => exact ⟨1, N.one_mem, by rw [pow_zero, pow_zero, one_mul]⟩
    | succ i ih =>
        obtain ⟨m, hm, hmi⟩ := ih
        refine ⟨e⁻¹ * m * e * n, N.mul_mem (hconj e he m hm) hn, ?_⟩
        rw [pow_succ, hmi, pow_succ]
        group
  have hpow_mem : ∀ x ∈ E ⊔ N, x ^ p ∈ N := by
    intro x hx
    have hx' : x ∈ (E : Set X) * (N : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right E N hEN]
      exact hx
    obtain ⟨e, he, n, hn, rfl⟩ := Set.mem_mul.mp hx'
    obtain ⟨m, hm, hm_eq⟩ := key e he n hn p
    rw [hm_eq, hE.2 e he, one_mul]
    exact hm
  have hcop : Nat.Coprime (2 ^ k) p :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm).pow_left k
  obtain ⟨j, -, hjm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have ht : 2 ^ k * j = 1 + p * ((2 ^ k * j) / p) := by
    conv_lhs => rw [← Nat.mod_add_div (2 ^ k * j) p]
    rw [hjm]
  have hhp : h ^ p ∈ N := hpow_mem h hh
  have hn1 : ((h ^ p) ^ ((2 ^ k * j) / p))⁻¹ ∈ N :=
    inv_mem (pow_mem hhp _)
  have hu1U : (h ^ (2 ^ k)) ^ j ∈ U := pow_mem hk j
  have hu1N : (h ^ (2 ^ k)) ^ j ∈ Subgroup.normalizer (N : Set X) :=
    hMN (hUH hu1U)
  have hnN : (h ^ (2 ^ k)) ^ j * ((h ^ p) ^ ((2 ^ k * j) / p))⁻¹
      * ((h ^ (2 ^ k)) ^ j)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp hu1N _).mp hn1
  have hu1_eq : (h ^ (2 ^ k)) ^ j = h * (h ^ p) ^ ((2 ^ k * j) / p) := by
    rw [← pow_mul]
    conv_lhs => rw [ht]
    rw [pow_add, pow_one, pow_mul]
  have h_eq : h = (h ^ (2 ^ k)) ^ j * ((h ^ p) ^ ((2 ^ k * j) / p))⁻¹ := by
    rw [hu1_eq, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨_, hnN, (h ^ (2 ^ k)) ^ j, hu1U, ?_⟩
  calc h = (h ^ (2 ^ k)) ^ j * ((h ^ p) ^ ((2 ^ k * j) / p))⁻¹ := h_eq
    _ = ((h ^ (2 ^ k)) ^ j * ((h ^ p) ^ ((2 ^ k * j) / p))⁻¹
          * ((h ^ (2 ^ k)) ^ j)⁻¹) * (h ^ (2 ^ k)) ^ j := by
        rw [mul_assoc, inv_mul_cancel, mul_one]

end CFSG.StandardType
