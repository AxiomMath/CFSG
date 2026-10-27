module

public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
public import CFSG.Sporadic.Bridge.M23Surj

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint Equiv
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks

namespace SporadicTwoCover

@[expose] def m23α : Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

@[expose] def m23β : Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem m23α_mem : m23α ∈ NativeSporadic.M23 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem m23β_mem : m23β ∈ NativeSporadic.M23 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def m23Word : List Char → Perm (Fin 23)
  | [] => 1
  | c :: w => (if c = 'a' then m23α else if c = 'b' then m23β else m23β⁻¹) * m23Word w

theorem m23Word_mem : ∀ w, m23Word w ∈ NativeSporadic.M23
  | [] => Subgroup.one_mem _
  | c :: w => by
    unfold m23Word
    refine Subgroup.mul_mem _ ?_ (m23Word_mem w)
    split_ifs
    · exact m23α_mem
    · exact m23β_mem
    · exact Subgroup.inv_mem _ m23β_mem

@[expose] def m23T : Perm (Fin 23) :=
  swap 0 9 * swap 1 6 * swap 2 3 * swap 4 19 * swap 5 13 * swap 7 8 * swap 11 15 * swap 16 21

@[expose] def m23N : Perm (Fin 23) :=
  List.formPerm [0, 7, 2, 1, 8, 6, 9] * List.formPerm [4, 13, 14, 15, 10, 12, 16] *
    List.formPerm [5, 17, 11, 20, 22, 21, 19]

theorem m23T_eq : m23T = m23Word "aBababaBaBaBababaBaBaBababaBaB".toList := by
  decide +kernel

theorem m23N_eq : m23N = m23Word "ababababaBaBabaB".toList := by
  decide +kernel

theorem m23T_mem : m23T ∈ NativeSporadic.M23 := m23T_eq ▸ m23Word_mem _

theorem m23N_mem : m23N ∈ NativeSporadic.M23 := m23N_eq ▸ m23Word_mem _

theorem m23_perm_e8Datum : E8Datum m23T (m23N * m23T * m23N⁻¹)
    (m23N * (m23N * m23T * m23N⁻¹) * m23N⁻¹) m23N where
  ne_one := by decide +kernel
  sq := by decide +kernel
  comm₁₂ := (by decide +kernel : m23T * (m23N * m23T * m23N⁻¹) = (m23N * m23T * m23N⁻¹) * m23T)
  comm₁₃ := (by decide +kernel : m23T * (m23N * (m23N * m23T * m23N⁻¹) * m23N⁻¹) =
    (m23N * (m23N * m23T * m23N⁻¹) * m23N⁻¹) * m23T)
  conj₁ := rfl
  conj₂ := rfl
  conj₃ := by decide +kernel

theorem m23_e8Datum :
    E8Datum (⟨m23T, m23T_mem⟩ : NativeSporadic.M23)
      (⟨m23N, m23N_mem⟩ * ⟨m23T, m23T_mem⟩ * ⟨m23N, m23N_mem⟩⁻¹)
      (⟨m23N, m23N_mem⟩ * (⟨m23N, m23N_mem⟩ * ⟨m23T, m23T_mem⟩ * ⟨m23N, m23N_mem⟩⁻¹) *
        ⟨m23N, m23N_mem⟩⁻¹) ⟨m23N, m23N_mem⟩ :=
  E8Datum.of_map NativeSporadic.M23.subtype Subtype.val_injective m23_perm_e8Datum

end SporadicTwoCover

open SporadicTwoCover

theorem noRankThreeTwoCover_m23 :
    NoRankThreeTwoCover (Spor .M23) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have h₀ : NoRankThreeTwoCover NativeSporadic.M23 := noRankThreeTwoCover_of_datum m23_e8Datum
  have e' : NativeSporadic.M23 ≃* Spor .M23 := e
  exact noRankThreeTwoCover_of_mulEquiv (X := NativeSporadic.M23) (Y := Spor .M23) e' h₀

end CFSG.RankThree.PartTwo.Sec4.Census
