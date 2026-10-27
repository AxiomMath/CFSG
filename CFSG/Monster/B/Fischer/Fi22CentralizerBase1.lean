
module


public import CFSG.Monster.B.Fischer.Fi22CoverBase1
public import CFSG.Monster.B.Fischer.Fi22CentralizerCheck
public import CFSG.LocalAnalysis.ComponentInitial.GroupComponents

@[expose] public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem fi22OuterM_le_P :
    fi22OuterM ≤ fi22P := by
  rw [fi22OuterM_eq]
  exact inf_le_left

theorem fi22OuterM_le_centralizer :
    fi22OuterM ≤ Subgroup.centralizer {fi22OuterZ} := by
  rw [fi22OuterM, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg
  rw [Set.mem_ofPred_eq, fi22OuterChainM, RawSchreierDatum.mem_ofArrays_original] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hi3 : i < 3 := hi
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact (eq_of_eqA (rep_compA rep_fi22OuterZ (rep_fi22OuterMStrong (by omega)))
    (rep_compA (rep_fi22OuterMStrong (by omega)) rep_fi22OuterZ)
    (fi22Centralizer_check.2.1 i hi3)).symm

theorem fi22OuterM_subgroupOf_index :
    (fi22OuterM.subgroupOf fi22P).index = 3510 := by
  have h := (fi22OuterM.subgroupOf fi22P).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22OuterM_le_P).toEquiv, card_fi22OuterM,
    card_fi22P] at h
  have h' : 18393661440 * (fi22OuterM.subgroupOf fi22P).index = 18393661440 * 3510 := by
    rw [h]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

end CFSG.Monster.B.Fischer
