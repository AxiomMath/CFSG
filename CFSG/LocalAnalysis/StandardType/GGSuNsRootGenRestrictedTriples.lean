module

public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenTriples
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNUnitGen

public section

namespace CFSG.StandardType

namespace QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

theorem iSup_coordBlockSU_card_three_avoid_pair_eq_top
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {N : ℕ} (hN : 4 ≤ N) (a b : Fin N) (hab : a ≠ b) :
    (⨆ (S : Finset (Fin N)) (_ : S.card = 3 ∧ ¬ (a ∈ S ∧ b ∈ S)),
      coordBlockSU K 2 1 S) = ⊤ := by
  classical
  refine top_le_iff.mp ?_
  rw [← iSup_coordBlockSU_card_three_eq_top hK hN]
  refine iSup₂_le fun S hS => ?_
  by_cases hbad : a ∈ S ∧ b ∈ S
  · obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := S) (t := Finset.univ)
      (by rw [Finset.card_univ, Fintype.card_fin, hS]; omega)
    let U := insert c S
    have hU : U.card = 4 := by
      change (insert c S).card = 4
      rw [Finset.card_insert_of_notMem hc, hS]
    have haU : a ∈ U := Finset.mem_insert_of_mem hbad.1
    have hbU : b ∈ U := Finset.mem_insert_of_mem hbad.2
    have hA : (U.erase a).card = 3 := by rw [Finset.card_erase_of_mem haU, hU]
    have hB : (U.erase b).card = 3 := by rw [Finset.card_erase_of_mem hbU, hU]
    have hAa : ¬ (a ∈ U.erase a ∧ b ∈ U.erase a) := by
      rintro ⟨ha, -⟩
      exact (Finset.mem_erase.mp ha).1 rfl
    have hBb : ¬ (a ∈ U.erase b ∧ b ∈ U.erase b) := by
      rintro ⟨-, hb⟩
      exact (Finset.mem_erase.mp hb).1 rfl
    have haB : a ∈ U.erase b := Finset.mem_erase.mpr ⟨hab, haU⟩
    have hAB : U.erase a ∪ U.erase b = U := by
      rw [Finset.erase_union_of_mem haB U]
      exact Finset.union_eq_left.mpr (Finset.erase_subset _ _)
    have h4 := coordBlockSU_sup_three hK hA hB (by rw [hAB, hU])
    rw [hAB] at h4
    refine (coordBlockSU_mono (Finset.subset_insert c S)).trans ?_
    rw [← h4]
    exact sup_le (le_iSup₂_of_le (U.erase a) ⟨hA, hAa⟩ le_rfl)
      (le_iSup₂_of_le (U.erase b) ⟨hB, hBb⟩ le_rfl)
  · exact le_iSup₂_of_le S ⟨hS, hbad⟩ le_rfl

end QTwo

namespace SuNsRootGen

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K] {d : ℕ}

theorem iSup_blockSU_triples_avoid_pair (h : UnitaryFieldData 2 1 K) (hd : 4 ≤ d)
    (a b : Fin d) (hab : a ≠ b) :
    (⨆ (S : Finset (Fin d)) (_ : S.card = 3 ∧ ¬ (a ∈ S ∧ b ∈ S)),
      TableBUE.blockSU (K := K) (n := 1) S) = ⊤ := by
  have := h.finite
  have := h.charP
  have key := congrArg (Subgroup.map (suEquivUnitarySU K 2 1 h.card_eq_sq d).toMonoidHom)
    (QTwo.iSup_coordBlockSU_card_three_avoid_pair_eq_top
      (h.card.trans (by norm_num)) hd a b hab)
  simpa only [Subgroup.map_iSup, coordBlockSU_map_suEquivUnitarySU,
    Subgroup.map_top_of_surjective (suEquivUnitarySU K 2 1 h.card_eq_sq d).toMonoidHom
      (suEquivUnitarySU K 2 1 h.card_eq_sq d).surjective] using key

end SuNsRootGen

end CFSG.StandardType

end
