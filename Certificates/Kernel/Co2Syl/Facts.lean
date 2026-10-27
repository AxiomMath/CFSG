module

public import Certificates.Kernel.Co2Syl.Checks
public import Certificates.Kernel.Co2Syl.Letters
public import CFSG.Certificates.Kernel.Co2Syl.Words
public import Certificates.Kernel.Co2Syl.Bind
public import Certificates.Kernel.Co2Syl.Lab6
public import Certificates.Kernel.Co2Syl.Lab8

public section

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.TabMatGrp CFSG.RankThree.Co2

theorem MatP_letter {l : ℕ} (hl : l < 42) : MatP 22 (lAt LT l) = rowsMat (letterRows l) :=
  (rowsMat_eq_MatP (letters l hl)).symm

theorem MatP_wordK {w : List ℕ} (hw : ∀ l ∈ w, l < 42) : MatP 22 (wordK w) = wordMat w :=
  MatP_foldR_eq (f := lAt LT) fun l hl => MatP_letter (hw l hl)

theorem wordK_lt : ∀ w : List ℕ, wordK w < 2 ^ 484
  | [] => IDP_lt
  | _ :: _ => mulV_lt _ _

theorem RP_eq {j : ℕ} (hj : j < 10) : RP j = wordK repWords[j]! := by
  rw [← RW_eq]
  exact Nat.eq_of_beq_eq_true (reps j hj)

theorem RP_lt {j : ℕ} (hj : j < 10) : RP j < 2 ^ 484 := by
  rw [RP_eq hj]
  exact wordK_lt _

theorem repMat_eq {j : ℕ} (hj : j < 10) : repMat j = MatP 22 (RP j) := by
  rw [RP_eq hj, MatP_wordK (repWords_lt j hj)]
  rfl

theorem genMon_five {G : ℕ → ℕ} {ws : Array (List ℕ)} (hs : ws.size = 5)
    (hw : ∀ k < 5, ∀ l ∈ ws[k]!, l < 42) (hg : ∀ j < 5, Nat.beq (G j) (wordK ws[j]!) = true) :
    genMon G = matGrp ws := by
  have e : ∀ j < 5, MatP 22 (G j) = wordMat ws[j]! := fun j hj => by
    rw [Nat.eq_of_beq_eq_true (hg j hj), MatP_wordK (hw j hj)]
  exact genMon_eq_matGrp (fun j hj => ⟨j, by omega, e j hj⟩) (fun k hk => ⟨k, by omega, e k (by omega)⟩)

theorem genMon1 : genMon G1 = matGrp pWords1 := genMon_five pWords1_size pWords1_lt gens1
theorem genMon3 : genMon G3 = matGrp pWords3 := genMon_five pWords3_size pWords3_lt gens3
theorem genMon5 : genMon G5 = matGrp pWords5 := genMon_five pWords5_size pWords5_lt gens5
theorem genMon6 : genMon G6 = matGrp pWords6 := genMon_five pWords6_size pWords6_lt gens6
theorem genMon8 : genMon G8 = matGrp pWords8 := genMon_five pWords8_size pWords8_lt gens8

theorem genMon4 : genMon G4 = matGrp pWords4 := by
  have e : ∀ j < 4, MatP 22 (G4 j) = wordMat pWords4[j]! := fun j hj => by
    rw [Nat.eq_of_beq_eq_true (gens4 j hj), MatP_wordK (pWords4_lt j hj)]
  have hs := pWords4_size
  refine genMon_eq_matGrp (fun j hj => ?_) fun k hk => ⟨k, by omega, e k (by omega)⟩
  rcases Nat.lt_or_ge j 4 with h | h
  · exact ⟨j, by rw [pWords4_size]; exact h, e j h⟩
  · have hj4 : j = 4 := by omega
    subst hj4
    exact ⟨3, by rw [pWords4_size]; omega, by rw [Nat.eq_of_beq_eq_true gens4pad]; exact e 3 (by omega)⟩

theorem tree1 : TreeRecs E1.CF G1 131072 :=
  ⟨blk_ok (nb := 2048) (by norm_num) blks1, Nat.eq_of_beq_eq_true zero1, Nat.eq_of_beq_eq_true one1,
    by decide⟩
theorem tree3 : TreeRecs E3.CF G3 65536 :=
  ⟨blk_ok (nb := 1024) (by norm_num) blks3, Nat.eq_of_beq_eq_true zero3, Nat.eq_of_beq_eq_true one3,
    by decide⟩
theorem tree4 : TreeRecs E4.CF G4 32768 :=
  ⟨blk_ok (nb := 512) (by norm_num) blks4, Nat.eq_of_beq_eq_true zero4, Nat.eq_of_beq_eq_true one4,
    by decide⟩
theorem tree5 : TreeRecs E5.CF G5 16384 :=
  ⟨blk_ok (nb := 256) (by norm_num) blks5, Nat.eq_of_beq_eq_true zero5, Nat.eq_of_beq_eq_true one5,
    by decide⟩
theorem tree6 : TreeRecs E6.CF G6 16384 :=
  ⟨blk_ok (nb := 256) (by norm_num) blks6, Nat.eq_of_beq_eq_true zero6, Nat.eq_of_beq_eq_true one6,
    by decide⟩
theorem tree8 : TreeRecs E8.CF G8 16384 :=
  ⟨blk_ok (nb := 256) (by norm_num) blks8, Nat.eq_of_beq_eq_true zero8, Nat.eq_of_beq_eq_true one8,
    by decide⟩

theorem facts1 : SylGrp pWords1 (2 ^ 17) [1] ∧ SqCount pWords1 (2 ^ 17) 1 2304 ∧
    SqCount pWords1 (2 ^ 17) 0 768 := by
  obtain ⟨s1, s0⟩ := sqCounts_of (hi := 32) tree1 genMon1 (RP_lt (by norm_num)) (RP_lt (by norm_num))
    (repMat_eq (by norm_num)) (repMat_eq (by norm_num)) (by norm_num) blks1
  rw [Nat.eq_of_beq_eq_true cnt1A] at s1
  rw [Nat.eq_of_beq_eq_true cnt1B] at s0
  refine ⟨sylGrp_of (Rp := RP) tree1 genMon1 ut1 ?_ ?_ ?_, s1, s0⟩ <;> intro j hj <;>
    simp only [List.mem_singleton] at hj <;> subst hj
  · exact repMat_eq (by norm_num)
  · exact ⟨_, mem1⟩
  · exact comm1

theorem facts3 : SylGrp pWords3 (2 ^ 16) [2, 3] ∧ SqCount pWords3 (2 ^ 16) 3 1152 ∧
    SqCount pWords3 (2 ^ 16) 0 384 := by
  obtain ⟨s1, s0⟩ := sqCounts_of (hi := 16) tree3 genMon3 (RP_lt (by norm_num)) (RP_lt (by norm_num))
    (repMat_eq (by norm_num)) (repMat_eq (by norm_num)) (by norm_num) blks3
  rw [Nat.eq_of_beq_eq_true cnt3A] at s1
  rw [Nat.eq_of_beq_eq_true cnt3B] at s0
  refine ⟨sylGrp_of (Rp := RP) tree3 genMon3 ut3 ?_ ?_ ?_, s1, s0⟩ <;> intro j hj <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj <;> rcases hj with rfl | rfl
  · exact repMat_eq (by norm_num)
  · exact repMat_eq (by norm_num)
  · exact ⟨_, mem3a⟩
  · exact ⟨_, mem3b⟩
  · exact comm3a
  · exact comm3b

theorem facts4 : SylGrp pWords4 (2 ^ 15) [4] ∧ SqCount pWords4 (2 ^ 15) 4 128 ∧
    SqCount pWords4 (2 ^ 15) 0 192 := by
  obtain ⟨s1, s0⟩ := sqCounts_of (hi := 8) tree4 genMon4 (RP_lt (by norm_num)) (RP_lt (by norm_num))
    (repMat_eq (by norm_num)) (repMat_eq (by norm_num)) (by norm_num) blks4
  rw [Nat.eq_of_beq_eq_true cnt4A] at s1
  rw [Nat.eq_of_beq_eq_true cnt4B] at s0
  refine ⟨sylGrp_of (Rp := RP) tree4 genMon4 ut4 ?_ ?_ ?_, s1, s0⟩ <;> intro j hj <;>
    simp only [List.mem_singleton] at hj <;> subst hj
  · exact repMat_eq (by norm_num)
  · exact ⟨_, mem4⟩
  · exact comm4

theorem facts5 : SylGrp pWords5 (2 ^ 14) [5, 6] ∧ SqCount pWords5 (2 ^ 14) 5 256 ∧
    SqCount pWords5 (2 ^ 14) 0 0 := by
  obtain ⟨s1, s0⟩ := sqCounts_of (hi := 4) tree5 genMon5 (RP_lt (by norm_num)) (RP_lt (by norm_num))
    (repMat_eq (by norm_num)) (repMat_eq (by norm_num)) (by norm_num) blks5
  rw [Nat.eq_of_beq_eq_true cnt5A] at s1
  rw [Nat.eq_of_beq_eq_true cnt5B] at s0
  refine ⟨sylGrp_of (Rp := RP) tree5 genMon5 ut5 ?_ ?_ ?_, s1, s0⟩ <;> intro j hj <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj <;> rcases hj with rfl | rfl
  · exact repMat_eq (by norm_num)
  · exact repMat_eq (by norm_num)
  · exact ⟨_, mem5a⟩
  · exact ⟨_, mem5b⟩
  · exact comm5a
  · exact comm5b

theorem facts6 : SylGrp pWords6 (2 ^ 14) [5, 6] ∧ ConjMul pWords6 (repMat 0) ∧
    (Nat.card (matGrp pWords6) ≤ 2 ^ 14 → ¬ ConjMul pWords6 (repMat 6)) := by
  refine ⟨sylGrp_of (Rp := RP) tree6 genMon6 ut6 ?_ ?_ ?_,
    conjMul_of tree6 genMon6 (repMat_eq (by norm_num)) wit6,
    not_conjMul_of tree6 genMon6 ut6 (repMat_eq (by norm_num)) lab6⟩ <;> intro j hj <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj <;> rcases hj with rfl | rfl
  · exact repMat_eq (by norm_num)
  · exact repMat_eq (by norm_num)
  · exact ⟨_, mem6a⟩
  · exact ⟨_, mem6b⟩
  · exact comm6a
  · exact comm6b

theorem facts8 : SylGrp pWords8 (2 ^ 14) [7, 8] ∧ ConjMul pWords8 (repMat 0) ∧
    (Nat.card (matGrp pWords8) ≤ 2 ^ 14 → ¬ ConjMul pWords8 (repMat 8)) := by
  refine ⟨sylGrp_of (Rp := RP) tree8 genMon8 ut8 ?_ ?_ ?_,
    conjMul_of tree8 genMon8 (repMat_eq (by norm_num)) wit8,
    not_conjMul_of tree8 genMon8 ut8 (repMat_eq (by norm_num)) lab8⟩ <;> intro j hj <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj <;> rcases hj with rfl | rfl
  · exact repMat_eq (by norm_num)
  · exact repMat_eq (by norm_num)
  · exact ⟨_, mem8a⟩
  · exact ⟨_, mem8b⟩
  · exact comm8a
  · exact comm8b

theorem sylFacts : SylFacts := ⟨facts1, facts3, facts4, facts5, facts6, facts8⟩

end CertificateChecks.KernelSpor.Co2Syl

end
