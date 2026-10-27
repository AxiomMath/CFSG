module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Background.Harris.R1

@[expose] def c3 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem c3_pow_three : c3 ^ 3 = 1 := by decide

theorem c3_four : c3 4 = 4 := by decide

theorem c3_sign : Equiv.Perm.sign c3 = 1 := by decide

theorem card_filter_commute_c3 :
    (Finset.univ.filter (fun p : Equiv.Perm (Fin 5) => p * c3 = c3 * p)).card = 6 := by
  decide +kernel

theorem card_centralizer_c3 : Nat.card ↥(Subgroup.centralizer ({c3} : Set (Equiv.Perm (Fin 5)))) = 6 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← card_filter_commute_c3]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem card_le_two_of_pGroup (P : Subgroup (Equiv.Perm (Fin 5))) (hP : IsPGroup 2 P)
    (hc : ∀ p ∈ P, p * c3 = c3 * p) : Nat.card ↥P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : P ≤ Subgroup.centralizer ({c3} : Set (Equiv.Perm (Fin 5))) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact (hc p hp).symm
  have hd : Nat.card ↥P ∣ 6 := card_centralizer_c3 ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  rw [hn] at hd ⊢
  have h2 : n ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have h4 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 hgt
    have := h4.trans hd
    omega
  calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h2
    _ = 2 := by norm_num

end CFSG.Quasithin.Background.Harris.R1
