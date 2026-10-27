module

public import CFSG.Sporadic.Co1Patterson.GenerationCount
public import CFSG.Sporadic.Co1Block.CentGA

public section

namespace CFSG.Sporadic.Co1Patterson

open Subgroup Equiv

theorem factorial_mul_pow_mul_factorial_ne : ∀ j < 11, ∀ m < 11, j % 2 = 1 →
    j.factorial * 2 ^ m * m.factorial ≠ 89181388800 ∧
      j.factorial * 2 ^ m * m.factorial ≠ 2 * 89181388800 := by
  decide

theorem exists_card_centralizer_perm {n : ℕ} {σ : Perm (Fin n)} (hσ : orderOf σ = 2) :
    ∃ m : ℕ, 1 ≤ m ∧ 2 * m ≤ n ∧ Nat.card (centralizer ({σ} : Set (Perm (Fin n)))) =
      (n - 2 * m).factorial * 2 ^ m * m.factorial := by
  have hp : (orderOf σ).Prime := hσ ▸ Nat.prime_two
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order hp
  rw [hσ] at hk
  have hle := Perm.sum_cycleType_le σ
  rw [hk, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hle
  refine ⟨k + 1, by omega, by omega, ?_⟩
  rw [Perm.nat_card_centralizer, hk]
  simp only [Multiset.sum_replicate, Multiset.prod_replicate, Fintype.card_fin, smul_eq_mul,
    Multiset.toFinset_replicate, Nat.add_one_ne_zero, ↓reduceIte, Finset.prod_singleton,
    Multiset.count_replicate_self]
  rw [mul_comm (k + 1) 2]

theorem card_centralizer_perm_eq_mul {n : ℕ} (hn : 2 ≤ n) (σ : alternatingGroup (Fin n)) :
    ∃ d : ℕ, d ∣ 2 ∧ Nat.card (centralizer ({(σ : Perm (Fin n))} : Set (Perm (Fin n)))) =
      d * Nat.card (centralizer ({σ} : Set (alternatingGroup (Fin n)))) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  refine ⟨(alternatingGroup (Fin n)).relIndex (centralizer {(σ : Perm (Fin n))}), ?_, ?_⟩
  · have h := Subgroup.relIndex_dvd_index_of_normal (alternatingGroup (Fin n))
      (centralizer {(σ : Perm (Fin n))})
    rwa [alternatingGroup.index_eq_two] at h
  · have h1 : Nat.card ((centralizer ({σ} : Set (alternatingGroup (Fin n)))).map
        (alternatingGroup (Fin n)).subtype) =
        Nat.card (centralizer ({σ} : Set (alternatingGroup (Fin n)))) :=
      Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective
    rw [map_centralizer_subtype] at h1
    rw [← h1, Subgroup.relIndex_mul_card]

theorem false_of_mulEquiv_alternatingGroup {X : Type*} [Group X] {t : X} (ht : orderOf t = 2)
    (hC : Nat.card (centralizer ({t} : Set X)) = 89181388800) {n : ℕ} (hn : Odd n)
    (φ : X ≃* alternatingGroup (Fin n)) : False := by
  have hσ : orderOf ((φ t : alternatingGroup (Fin n)) : Perm (Fin n)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  obtain ⟨m, hm1, hm2, hcard⟩ := exists_card_centralizer_perm hσ
  obtain ⟨d, hd, hd'⟩ := card_centralizer_perm_eq_mul (by omega) (φ t)
  rw [← CFSG.Sporadic.Co1Block.card_centralizer_equiv φ t, hC, hcard] at hd'
  have hd12 : d = 1 ∨ d = 2 := (Nat.dvd_prime Nat.prime_two).mp hd
  have h11 : ¬ 11 ∣ d * 89181388800 := by
    rcases hd12 with rfl | rfl <;> norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hm : m < 11 := by
    by_contra h
    exact h11 (hd' ▸ dvd_mul_of_dvd_right (hp11.dvd_factorial.mpr (by omega)) _)
  have hj : n - 2 * m < 11 := by
    by_contra h
    exact h11 (hd' ▸ dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (hp11.dvd_factorial.mpr (by omega)) _) _)
  have hodd : (n - 2 * m) % 2 = 1 := by
    obtain ⟨k, rfl⟩ := hn
    omega
  obtain ⟨h1, h2⟩ := factorial_mul_pow_mul_factorial_ne (n - 2 * m) hj m hm hodd
  rcases hd12 with rfl | rfl
  · exact h1 (hd'.trans (one_mul _))
  · exact h2 hd'

end CFSG.Sporadic.Co1Patterson
