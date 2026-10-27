
module

public import CFSG.Monster.B.Fischer.Fi22LocalBase

public import CFSG.Monster.B.Fischer.Fi22LocalCheck
public import CFSG.Monster.B.Fischer.Fi22OuterBase

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem fi22OuterChainM_arrays : ChainArrays fi22OuterChainM
    ((fi22OuterStrong3510 3).extract 0 fi22OuterMGenCount) (fi22OuterStrong3510 3)
    #[0, 1, 2, 6, 4, 3] (fi22WordsArr fi22OuterMGenCount 17 fi22OuterMDerivations) := by
  have h := chainArrays_ofArrays (n := 3510) (hn := by decide) (k := fi22OuterMGenCount)
    (hk := by rw [fi22OuterStrong3510, Array.size_ofFn]; decide)
    (base := fi22FinList 3510 (by decide) fi22OuterMBase) (hb := by decide)
    (W := fi22WordsArr fi22OuterMGenCount 17 fi22OuterMDerivations)
    (chainCheckFacts fi22Local_check.1).strong_inv
  have hb : ((fi22FinList 3510 (by decide) fi22OuterMBase).map Fin.val).toArray =
      #[0, 1, 2, 6, 4, 3] := rfl
  rw [hb] at h
  exact h

theorem fi22OuterChainT_arrays : ChainArrays fi22OuterChainT
    ((fi22OuterStrong3510 4).extract 0 fi22OuterTGenCount) (fi22OuterStrong3510 4)
    #[0, 1, 2, 3, 6, 4] (fi22WordsArr fi22OuterTGenCount 13 fi22OuterTDerivations) := by
  have h := chainArrays_ofArrays (n := 3510) (hn := by decide) (k := fi22OuterTGenCount)
    (hk := by rw [fi22OuterStrong3510, Array.size_ofFn]; decide)
    (base := fi22FinList 3510 (by decide) fi22OuterTBase) (hb := by decide)
    (W := fi22WordsArr fi22OuterTGenCount 13 fi22OuterTDerivations)
    (chainCheckFacts fi22Local_check.2.2.1).strong_inv
  have hb : ((fi22FinList 3510 (by decide) fi22OuterTBase).map Fin.val).toArray =
      #[0, 1, 2, 3, 6, 4] := rfl
  rw [hb] at h
  exact h

theorem fi22OuterChainM_valid : ValidSchreier fi22OuterChainM :=
  (validSchreier_of_chainOK fi22OuterChainM_arrays (by norm_num) fi22Local_check.1).1

theorem fi22OuterChainT_valid : ValidSchreier fi22OuterChainT :=
  (validSchreier_of_chainOK fi22OuterChainT_arrays (by norm_num) fi22Local_check.2.2.1).1

theorem card_fi22OuterM : Nat.card fi22OuterM = 18393661440 := by
  rw [fi22OuterM, card_originalSubgroup_of_chainOK fi22OuterChainM_arrays (by norm_num)
    fi22Local_check.1, fi22Local_check.2.1]
  rfl

theorem card_fi22OuterT : Nat.card fi22OuterT = 131072 := by
  rw [fi22OuterT, card_originalSubgroup_of_chainOK fi22OuterChainT_arrays (by norm_num)
    fi22Local_check.2.2.1, fi22Local_check.2.2.2.1]
  rfl

theorem rep_fi22OuterMStrong {k : ℕ} (hk : k < 17) :
    Rep 3510 (fi22OuterStrong3510 3)[k]! (permOfArr 3510 (fi22OuterStrong3510 3)[k]!) :=
  (rep_permOfArr ((chainCheckFacts fi22Local_check.1).strong_inv k
    (by rw [fi22OuterStrong3510, Array.size_ofFn]; exact hk))).1

theorem rep_fi22OuterTStrong {k : ℕ} (hk : k < 13) :
    Rep 3510 (fi22OuterStrong3510 4)[k]! (permOfArr 3510 (fi22OuterStrong3510 4)[k]!) :=
  (rep_permOfArr ((chainCheckFacts fi22Local_check.2.2.1).strong_inv k
    (by rw [fi22OuterStrong3510, Array.size_ofFn]; exact hk))).1

theorem fi22OuterM_le :
    fi22OuterM ≤ fi22P ⊓ MulAction.stabilizer (Equiv.Perm (Fin 3510)) (0 : Fin 3510) := by
  rw [fi22OuterM, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg
  rw [Set.mem_ofPred_eq, fi22OuterChainM, RawSchreierDatum.mem_ofArrays_original] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hi3 : i < 3 := hi
  have hrep := rep_fi22OuterMStrong (k := i) (by omega)
  refine ⟨mem_fi22P_of_siftA hrep (fi22Local_check.2.2.2.2.1 i hi3),
    MulAction.mem_stabilizer_iff.2 ?_⟩
  rw [Equiv.Perm.smul_def]
  apply Fin.ext
  rw [← hrep 0]
  exact fi22Local_check.2.2.2.2.2.1 i hi3

theorem fi22OuterT_le :
    fi22OuterT ≤ fi22P := by
  rw [fi22OuterT, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg
  rw [Set.mem_ofPred_eq, fi22OuterChainT, RawSchreierDatum.mem_ofArrays_original] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hi9 : i < 9 := hi
  exact mem_fi22P_of_siftA (rep_fi22OuterTStrong (k := i) (by omega))
    (fi22Local_check.2.2.2.2.2.2 i hi9)

theorem fi22OuterM_eq :
    fi22OuterM = fi22P ⊓ MulAction.stabilizer (Equiv.Perm (Fin 3510)) (0 : Fin 3510) :=
  Subgroup.eq_of_le_of_card_ge fi22OuterM_le
    (by rw [card_fi22P_inf_stabilizer, card_fi22OuterM])

theorem fi22OuterT_sylow :
    ∃ S : Sylow 2 fi22P, (S : Subgroup fi22P) = fi22OuterT.subgroupOf fi22P := by
  have hcard : Nat.card (fi22OuterT.subgroupOf fi22P) = 2 ^ (Nat.card fi22P).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22OuterT_le).toEquiv, card_fi22OuterT,
      factorization_card_fi22P_two]
    norm_num
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem AT_Fi22_local_subgroup_orders :
    fi22OuterM = fi22P ⊓ MulAction.stabilizer (Equiv.Perm (Fin 3510)) (0 : Fin 3510) ∧
    Nat.card fi22OuterM = 18393661440 ∧
    fi22OuterT ≤ fi22P ∧ Nat.card fi22OuterT = 131072 ∧
    (∃ S : Sylow 2 fi22P, (S : Subgroup fi22P) = fi22OuterT.subgroupOf fi22P) ∧
    ValidSchreier fi22OuterChainM ∧ ValidSchreier fi22OuterChainT ∧
    (∀ p ∈ ([0, 1, 2, 3, 6, 4] : List (Fin 3510)), p ∈ fi22OuterChainM.base.toList) ∧
    (∀ p ∈ ([0, 1, 2, 3, 6, 4] : List (Fin 3510)), p ∈ fi22OuterChainT.base.toList) := by
  refine ⟨fi22OuterM_eq, card_fi22OuterM, fi22OuterT_le, card_fi22OuterT, fi22OuterT_sylow,
    fi22OuterChainM_valid, fi22OuterChainT_valid, ?_, ?_⟩
  · rw [fi22OuterChainM, RawSchreierDatum.ofArrays_base_toList]
    simp [fi22FinList, fi22OuterMBase]
  · rw [fi22OuterChainT, RawSchreierDatum.ofArrays_base_toList]
    simp [fi22FinList, fi22OuterTBase]

end CFSG.Monster.B.Fischer
