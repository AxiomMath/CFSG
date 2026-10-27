module

public import CFSG.Sporadic.SmallOddCore.LocalSpec
import Certificates.Kernel.TwoHS.HarSylGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl

public section

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier CFSG.KD.TwoHS CFSG.KS CFSG.KS.PEnum

namespace Certificates

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native in
theorem certificate26131 :
    (∀ g ∈ harU ++ harWgens, permOK 11200 g = true) ∧
    Nat.card (genOf 11200 harU) = 1024 ∧ Nat.card (genOf 11200 harCgens) = 128 ∧
    Nat.card (genOf 11200 harWgens) = 512 ∧
    Nat.card ↥(genOf 11200 harU ⊓
      Subgroup.centralizer (genOf 11200 harU : Set (Equiv.Perm (Fin 11200)))) = 4 ∧
    (∀ c : Equiv.Perm (Fin 11200), Rep 11200 harC0 c →
      Nat.card {y : genOf 11200 harU // (y : Equiv.Perm (Fin 11200)) ^ 2 = c} = 80 ∧
      Nat.card {y : genOf 11200 harCgens // (y : Equiv.Perm (Fin 11200)) ^ 2 = c} = 16 ∧
      Nat.card {y : genOf 11200 harWgens // (y : Equiv.Perm (Fin 11200)) ^ 2 = c} = 48 ∧
      c ∈ genOf 11200 harCgens ∧ c * c = 1 ∧ c ≠ 1) ∧
    (∀ z : Equiv.Perm (Fin 11200), Rep 11200 harZ1 z →
      Nat.card {y : genOf 11200 harU // (y : Equiv.Perm (Fin 11200)) ^ 2 = z} = 64 ∧
      Nat.card {y : genOf 11200 harCgens // (y : Equiv.Perm (Fin 11200)) ^ 2 = z} = 32 ∧
      orderOf z = 2 ∧ ∀ g ∈ harU, z * CFSG.Sporadic.SmallOddCore.tp 11200 g = CFSG.Sporadic.SmallOddCore.tp 11200 g * z) ∧
    (∀ z : Equiv.Perm (Fin 11200), Rep 11200 harZ2 z →
      Nat.card {y : genOf 11200 harU // (y : Equiv.Perm (Fin 11200)) ^ 2 = z} = 48 ∧
      Nat.card {y : genOf 11200 harCgens // (y : Equiv.Perm (Fin 11200)) ^ 2 = z} = 16 ∧
      Nat.card {y : genOf 11200 harWgens // (y : Equiv.Perm (Fin 11200)) ^ 2 = z} = 16) ∧
    (∀ c z : Equiv.Perm (Fin 11200), Rep 11200 harC0 c → Rep 11200 harZ1 z →
      z ≠ c ∧ c * z ≠ z ∧ z ≠ 1 ∧ c * z ≠ c ∧ c * z ≠ 1) ∧
    ∀ y ∈ genOf 11200 harU, y ^ 2 = 1 → y ∈ genOf 11200 harWgens := by
  obtain ⟨hT, hZ1, hZ2, hTT, hZZ, hT0, hZ0, hZ20, hZT, hZ2T, hZ2Z⟩ := sy_pts
  have sqE := ch26131_sqE
  have sqC := ch26131_sqC
  have sqW := ch26131_sqW
  simp only [bAnd_iff] at sqE sqC sqW
  have pts2 := ch26131_pts2
  simp only [bAnd_iff] at pts2
  have hcT : syE syT * syE syT = 1 := by
    rw [← (syMul_eq hT hT).2, hTT, syE_zero]
  have hzZ : syE syZ1 * syE syZ1 = 1 := by
    rw [← (syMul_eq hZ1 hZ1).2, hZZ, syE_zero]
  have hne : ∀ {a b : Nat}, a < 1024 → b < 1024 → a ≠ b → syE a ≠ syE b :=
    fun ha hb h e => h (syE_inj ha hb e)
  refine ⟨?_, ?_, ?_, ?_, sy_centre, ?_, ?_, ?_, ?_, fun y hy hy2 => sy_inv hy hy2⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact sy_perm_harU g hg
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      exact CFSG.KC.BfsPairs.permOK_of_rep (syH_rep j hj)
  · exact (CFSG.Sporadic.SmallOddCore.enumOK_spec sy_hn sy_perm_harU sy_enum).1
  · exact sy_card_all syC_set (sy_list_inj syCP.1)
  · exact sy_card_all syW_set (sy_list_inj syWP.1)
  · intro c hc
    rw [rep_unique hc syT_rep]
    refine ⟨?_, ?_, ?_, ?_, hcT, ?_⟩
    · rw [sy_cnt_T0 hT]
      exact Nat.eq_of_beq_eq_true sqE.1
    · rw [sy_cnt_C hT]
      exact Nat.eq_of_beq_eq_true sqC.1
    · rw [sy_cnt_W hT]
      exact Nat.eq_of_beq_eq_true sqW.1
    · have hq : r32 CPI syT < 128 := Nat.le_of_ble_eq_true pts2.1
      have hm : syE syT ∈ (genOf 11200 harCgens : Set (Equiv.Perm (Fin 11200))) := by
        rw [syC_set]
        refine ⟨r32 CPI syT, hq, ?_⟩
        change syE (r32 CPos (r32 CPI syT)) = syE syT
        rw [syCP.2.1 _ hT hq]
      exact hm
    · rw [← syE_zero]
      exact hne hT (by norm_num) hT0
  · intro z hz
    rw [rep_unique hz syZ1_rep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [sy_cnt_T0 hZ1]
      exact Nat.eq_of_beq_eq_true sqE.2.1
    · rw [sy_cnt_C hZ1]
      exact Nat.eq_of_beq_eq_true sqC.2.1
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime (by rw [pow_two]; exact hzZ) ?_
      rw [← syE_zero]
      exact hne hZ1 (by norm_num) hZ0
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hj3 : j < 3 := by rwa [syU_len] at hj
      rw [← syG_eq_tp hj]
      exact ((sy_comm_iff hZ1 hj3).1 (CFSG.KS.Raw.Orb.allN_iff.1 pts2.2 j hj3)).symm
  · intro z hz
    rw [rep_unique hz syZ2_rep]
    refine ⟨?_, ?_, ?_⟩
    · rw [sy_cnt_T0 hZ2]
      exact Nat.eq_of_beq_eq_true sqE.2.2
    · rw [sy_cnt_C hZ2]
      exact Nat.eq_of_beq_eq_true sqC.2.2
    · rw [sy_cnt_W hZ2]
      exact Nat.eq_of_beq_eq_true sqW.2
  · intro c z hc hz
    rw [rep_unique hc syT_rep, rep_unique hz syZ1_rep, ← syZ2_eq]
    refine ⟨hne hZ1 hT hZT, hne hZ2 hZ1 hZ2Z, ?_, hne hZ2 hT hZ2T, ?_⟩
    · rw [← syE_zero]
      exact hne hZ1 (by norm_num) hZ0
    · rw [← syE_zero]
      exact hne hZ2 (by norm_num) hZ20

end Certificates
