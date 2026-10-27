module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQCount
public import CFSG.Monster.B.GSide.HInnerFusionI3CertInputs

public section

namespace CertificateChecks.KernelBM.CTIB.Hist

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.Monster.B.GSide CFSG.KC.Bfs
  CertificateChecks.KernelBM.CTIB CertificateChecks.KernelBM.CTIB.CosetQ
  CertificateChecks.KernelBM.CTIB.QK CertificateChecks.KernelBM.CTIB.Inner

open Classical

set_option maxRecDepth 100000

theorem xor7_mod (n : ℕ) : (n ^^^ 7) % 2 ^ 22 = n % 2 ^ 22 ^^^ 7 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  by_cases hi : i < 22
  · simp [hi]
  · have h7 : (7 : ℕ).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : (7 : ℕ) < 2 ^ 22)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, h7]

section Census

variable (hC : CensusLists)
include hC

theorem tab_iff {k v : ℕ} (hk : k < 5) (h0 : 0 < v) (h1 : v < 2 ^ 22) :
    innerTab[v]! = k + 1 ↔ v ∈ S k := by
  refine ⟨fun h => ?_, tab_S hC hk⟩
  obtain ⟨j, hj, hm⟩ := S_cover hC h0 h1
  have e := tab_S hC hj hm
  rw [h] at e
  rw [Nat.succ_inj.1 e]
  exact hm

theorem innerTy_iff {k n : ℕ} (hk : k < 5) : innerTy innerTab n = k + 1 ↔ n % 2 ^ 22 ∈ S k := by
  have hlt : n % 2 ^ 22 < 2 ^ 22 := Nat.mod_lt _ (Nat.two_pow_pos 22)
  unfold innerTy
  by_cases h0 : n % 2 ^ 22 = 0
  · rw [if_pos h0, h0]
    refine ⟨fun h => ?_, fun h => absurd (S_valid hC hk h).1 (Nat.lt_irrefl 0)⟩
    split_ifs at h <;> omega
  · rw [if_neg h0]
    exact tab_iff hC hk (Nat.pos_of_ne_zero h0) hlt

theorem frameA_iff (n : ℕ) :
    frameA innerTab n = true ↔ (n % 2 ^ 22 ∈ S 0 ∧ Rc 2 7 (n % 2 ^ 22)) := by
  have hq : qmul gArr n 7 % 2 ^ 22 = 7 ^^^ n % 2 ^ 22 := by
    rw [qmul_mod, xor7_mod, Nat.xor_comm]
  have h1 : innerTy innerTab n = 1 ↔ n % 2 ^ 22 ∈ S 0 := innerTy_iff hC (k := 0) (by omega)
  have h3 : innerTy innerTab (qmul gArr n 7) = 3 ↔ 7 ^^^ n % 2 ^ 22 ∈ S 2 := by
    rw [← hq]
    exact innerTy_iff hC (k := 2) (by omega)
  have hc : qmul gArr n 7 = qmul gArr 7 n ↔ bt 7 (n % 2 ^ 22) = false := by
    rw [comm_iff, ← bt_mod n 7, bt_comm]
  unfold frameA Rc
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq, h1, h3, hc]
  exact and_assoc

end Census

theorem frameA_count (hC : CensusLists) : countBelow (frameA innerTab) (2 ^ 23) 0 = 2240 := by
  have e3 : Nat.count (fun v => v ∈ S 0 ∧ Rc 2 7 v) (2 ^ 22) = cnt (Rc 2) 0 (rootOf 2) := by
    have r2 : rootOf 2 = 7 := rfl
    rw [Nat.count_eq_card_filter_range, cnt, r2]
    refine congrArg Finset.card (Finset.ext fun v => ?_)
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨(S_valid hC (by omega) h.1).2, h⟩⟩
  have e4 := cnt0_eq hC (a := 2) (c := 2) (by omega) (by omega)
  rw [countBelow_eq, Nat.zero_add, (by norm_num : (2 : ℕ) ^ 23 = 2 ^ 22 * 2),
    count_congr' (q := fun n => n % 2 ^ 22 ∈ S 0 ∧ Rc 2 7 (n % 2 ^ 22)) fun m _ => frameA_iff hC m]
  refine (count_mod (fun v => v ∈ S 0 ∧ Rc 2 7 v) (2 ^ 22) 2).trans ?_
  rw [e3, e4]
  rfl

end CertificateChecks.KernelBM.CTIB.Hist

end
