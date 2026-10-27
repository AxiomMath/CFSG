module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowA10

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open Equiv Equiv.Perm
open CFSG.Quasithin.SteinbergCB (conjPerm conjPerm_surjective conjPerm_injective)

theorem exists_card_centralizer_of_pow_three {n : ℕ} {τ : Perm (Fin n)} (h3 : τ ^ 3 = 1)
    (h1 : τ ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ 3 * k ≤ n ∧
      Nat.card (Subgroup.centralizer ({τ} : Set (Perm (Fin n)))) =
        (n - 3 * k).factorial * 3 ^ k * k.factorial := by
  have hord : orderOf τ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hmem : ∀ m ∈ τ.cycleType, m = 3 := fun m hm => by
    have h2 := two_le_of_mem_cycleType hm
    have hd := (dvd_of_mem_cycleType hm).trans hord
    have : m ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    interval_cases m
    · norm_num at hd
    · rfl
  set k := Multiset.card τ.cycleType with hk
  have hrep : τ.cycleType = Multiset.replicate k 3 := Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hsum : 3 * k ≤ n := by
    have := sum_cycleType_le τ
    rw [hrep, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at this
    omega
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, Multiset.replicate_zero] at hrep
    exact h1 (cycleType_eq_zero.mp hrep)
  refine ⟨k, hk1, hsum, ?_⟩
  rw [nat_card_centralizer, hrep, Multiset.sum_replicate, Multiset.prod_replicate,
    Fintype.card_fin, smul_eq_mul, Multiset.toFinset_replicate, if_neg (by omega),
    Finset.prod_singleton, Multiset.count_replicate_self, mul_comm k 3]

theorem card_centralizer_le_nine {τ : Perm (Fin 9)} (h3 : τ ^ 3 = 1) (h1 : τ ≠ 1) :
    Nat.card (Subgroup.centralizer ({τ} : Set (Perm (Fin 9)))) ≤ 2160 := by
  obtain ⟨k, hk1, hk3, hc⟩ := exists_card_centralizer_of_pow_three h3 h1
  rw [hc]
  have : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases this with rfl | rfl | rfl <;> decide

theorem noCfgS429_alternatingGroup_nine :
    NoCfgS429 (alternatingGroup (Fin 9)) := by
  intro A σ K hc
  obtain ⟨τ, rfl⟩ := conjPerm_surjective (by norm_num : 9 = 5 ∨ 7 ≤ 9) σ
  have hτ3 : τ ^ 3 = 1 := conjPerm_injective (by norm_num)
    (by rw [map_pow, hc.isE27.1.2 _ hc.mem, map_one])
  have hτ1 : τ ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
  haveI := hc.isPerfect
  have h1 := le_card_of_isType429 hc.isType
  have h2 : Nat.card (K ⧸ CFSG.pCore 2 K) ≤ Nat.card K :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have h3 : Nat.card K ≤ Nat.card (autFix (conjPerm 9 τ)) :=
    Subgroup.card_le_of_le hc.le_autFix
  have h4 := card_autFix_conjPerm_le τ
  have h5 := card_centralizer_le_nine hτ3 hτ1
  omega

theorem rowSOf429_alternatingGroup_nine :
    RowSOf429 (alternatingGroup (Fin 9)) :=
  rowSOf429_of_noCfgS429 noCfgS429_alternatingGroup_nine

end CFSG.RankThree.PartTwo.Sec4.RonanK429
