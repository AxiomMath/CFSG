module

public import Certificates.Certificate707011
public import CFSG.LocalAnalysis.StandardType.GGTriD4TwoRow.Model
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434D42

open Subgroup CFSG.Open

theorem card_le_three_mul_card_inf_d4P
    {B : Subgroup (Equiv.Perm (Fin 2457))} (hBG : B ≤ d4G) :
    Nat.card B ≤ 3 * Nat.card ↥(B ⊓ d4P) := by
  have := d4P_normal_d4G
  have h := (d4P.subgroupOf d4G).relIndex_mul_card (B.subgroupOf d4G)
  have hd : (d4P.subgroupOf d4G).relIndex (B.subgroupOf d4G) ∣ 3 :=
    index_d4P_d4G ▸ Subgroup.relIndex_dvd_index_of_normal _ _
  have hB : Nat.card ↥(B.subgroupOf d4G) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv
  have hI : Nat.card ↥(d4P.subgroupOf d4G ⊓ B.subgroupOf d4G) = Nat.card ↥(B ⊓ d4P) := by
    have hI' : d4P.subgroupOf d4G ⊓ B.subgroupOf d4G = (B ⊓ d4P).subgroupOf d4G := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact and_comm
    rw [hI']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hBG)).toEquiv
  rw [hB, hI] at h
  rw [← h]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (by norm_num) hd)

theorem exists_normalizer_moving_or_solvable
    (hrk : ∀ E : Subgroup (Equiv.Perm (Fin 2457)), E ≤ d4P → IsElemAbelian 3 E → Nat.card E ≤ 9)
    {B : Subgroup (Equiv.Perm (Fin 2457))} (hBG : B ≤ d4G) (hB : IsElemAbelian 3 B)
    (h27 : 27 ≤ Nat.card B) {u : Equiv.Perm (Fin 2457)} (huB : u ∈ B) (huP : u ∈ d4P)
    (hu1 : u ≠ 1) :
    IsSolvable ↥(centralizer {u} ⊓ d4P) ∨
      ∃ n ∈ d4P, n ∈ normalizer (B : Set (Equiv.Perm (Fin 2457))) ∧ n * u * n⁻¹ ∉ zpowers u := by
  have hBP9 : Nat.card ↥(B ⊓ d4P) ≤ 9 := hrk _ inf_le_right (hB.mono inf_le_left)
  have hB3 := card_le_three_mul_card_inf_d4P hBG
  have hBc : Nat.card B = 27 := by omega
  have hBP : ¬ B ≤ d4P := fun h => by
    rw [inf_of_le_left h] at hBP9
    omega
  exact Certificates.certificate707011 B hBG hB hBc hBP u huB huP hu1

end CFSG.RankThree.PartTwo.Sec4.Item434D42
