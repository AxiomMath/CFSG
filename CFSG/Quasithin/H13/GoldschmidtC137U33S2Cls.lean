module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Cnt

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit

variable {B : Subgroup Gam}

theorem cls_Q (hB : B ≤ sSubG) (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hff : 64 ≤ (idx B).card * Nat.card (fixV (B.map (g2QAct (ZMod 2))))) :
    ∃ e < 8, (∀ l, l ∈ idx B ↔ l ∈ sE8.getD e []) ∧ 8 ≤ cntQ (sE8.getD e []) := by
  classical
  let P : ℕ → Bool := fun c => decide (∀ i ∈ idx B, fixQB (sM i) c = true)
  have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixQB (sM i) c.1 = true := fun c => by
    simp [P]
  have hC := card_fixV_Q hB P hP
  have hCi : ∀ i ∈ idx B, Nat.card (fixV (B.map (g2QAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => !c.testBit 0 && fixQB (sM i) c).length := fun i hi => by
    rw [hC]
    refine length_filter_le fun c hc => ?_
    simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [Bool.and_eq_true]
    exact ⟨hc.1, hc.2 i hi⟩
  have hCij : ∀ i ∈ idx B, ∀ j ∈ idx B, Nat.card (fixV (B.map (g2QAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => !c.testBit 0 && (fixQB (sM i) c && fixQB (sM j) c)).length :=
    fun i hi j hj => by
      rw [hC]
      refine length_filter_le fun c hc => ?_
      simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨hc.1, hc.2 i hi, hc.2 j hj⟩
  have hsingle : ∀ i ∈ idx B, i ≠ 0 →
      (o0Codes.filter fun c => !c.testBit 0 && fixQB (sM i) c).length ≤ 16 := by
    intro i hi hi0
    rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
    · rw [(sInner_fix i h).2]
    · rw [(sOuter_fix i h).2]
      norm_num
  rcases pow_two_cases (card_idx_pow hB hB2) with hn | hn | hn | h8
  · exact absurd (Subgroup.eq_bot_of_card_eq B (by rw [card_eq_idx hB, hn])) hB1
  · exfalso
    obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    rw [Finset.mem_singleton] at hi0
    have h1 := (hCi i hi).trans (hsingle i hi hi0)
    rw [hn] at hff
    omega
  · exfalso
    obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, i} : Finset ℕ)) (t := idx B)
      (by have := Finset.card_le_two (a := 0) (b := i); rw [hn]; omega)
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hi0 hj0
    rw [hn] at hff
    have hbound : Nat.card (fixV (B.map (g2QAct (ZMod 2)))) < 16 := by
      rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
      · rcases List.mem_append.1 (idx_inv hB2 hj hj0.1) with h' | h'
        · exact (hCij i hi j hj).trans_lt
            (sInner_pair i h j h' (Ne.symm hj0.2) (idx_comm hBc hi hj)).2
        · have := (hCi j hj).trans_eq (sOuter_fix j h').2
          omega
      · have := (hCi i hi).trans_eq (sOuter_fix i h).2
        omega
    omega
  · have hcard8 := card_idx_le_8 hB hB2 hBc h8
    obtain ⟨e, he, hiff⟩ := idx_eq_sE8 hB hB2 hBc h8
    have hfilter : (o0Codes.filter fun c => !c.testBit 0 && P c) =
        o0Codes.filter fun c => !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c := by
      refine List.filter_congr fun c _ => ?_
      congr 1
      simp only [P]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true]
      exact forall_congr' fun i => imp_congr (hiff i) Iff.rfl
    refine ⟨e, he, hiff, ?_⟩
    rw [hcard8] at hff
    have : Nat.card (fixV (B.map (g2QAct (ZMod 2)))) = cntQ (sE8.getD e []) := by
      rw [hC, hfilter]
      rfl
    omega

theorem cls_O (hB : B ≤ sSubG) (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hff : 128 ≤ (idx B).card * Nat.card (fixV (B.map (g2OAct (ZMod 2))))) :
    ∃ e < 8, (∀ l, l ∈ idx B ↔ l ∈ sE8.getD e []) ∧ 16 ≤ cntO (sE8.getD e []) := by
  classical
  let P : ℕ → Bool := fun c => decide (∀ i ∈ idx B, fixOB (sM i) c = true)
  have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixOB (sM i) c.1 = true := fun c => by
    simp [P]
  have hC := card_fixV_O hB P hP
  have hCi : ∀ i ∈ idx B, Nat.card (fixV (B.map (g2OAct (ZMod 2)))) ≤
      (o0Codes.filter (fixOB (sM i))).length := fun i hi => by
    rw [hC]
    exact length_filter_le fun c hc => by simp only [P, decide_eq_true_eq] at hc; exact hc i hi
  have hCij : ∀ i ∈ idx B, ∀ j ∈ idx B, Nat.card (fixV (B.map (g2OAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => fixOB (sM i) c && fixOB (sM j) c).length := fun i hi j hj => by
    rw [hC]
    refine length_filter_le fun c hc => ?_
    simp only [P, decide_eq_true_eq] at hc
    simp [hc i hi, hc j hj]
  have hsingle : ∀ i ∈ idx B, i ≠ 0 → (o0Codes.filter (fixOB (sM i))).length ≤ 32 := by
    intro i hi hi0
    rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
    · rw [(sInner_fix i h).1]
    · rw [(sOuter_fix i h).1]
      norm_num
  rcases pow_two_cases (card_idx_pow hB hB2) with hn | hn | hn | h8
  · exact absurd (Subgroup.eq_bot_of_card_eq B (by rw [card_eq_idx hB, hn])) hB1
  · exfalso
    obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    rw [Finset.mem_singleton] at hi0
    have h1 := (hCi i hi).trans (hsingle i hi hi0)
    rw [hn] at hff
    omega
  · exfalso
    obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, i} : Finset ℕ)) (t := idx B)
      (by have := Finset.card_le_two (a := 0) (b := i); rw [hn]; omega)
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hi0 hj0
    rw [hn] at hff
    have hbound : Nat.card (fixV (B.map (g2OAct (ZMod 2)))) < 32 := by
      rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
      · rcases List.mem_append.1 (idx_inv hB2 hj hj0.1) with h' | h'
        · exact (hCij i hi j hj).trans_lt
            (sInner_pair i h j h' (Ne.symm hj0.2) (idx_comm hBc hi hj)).1
        · have := (hCi j hj).trans_eq (sOuter_fix j h').1
          omega
      · have := (hCi i hi).trans_eq (sOuter_fix i h).1
        omega
    omega
  · have hcard8 := card_idx_le_8 hB hB2 hBc h8
    obtain ⟨e, he, hiff⟩ := idx_eq_sE8 hB hB2 hBc h8
    have hfilter : (o0Codes.filter P) =
        o0Codes.filter fun c => (sE8.getD e []).all fun i => fixOB (sM i) c := by
      refine List.filter_congr fun c _ => ?_
      simp only [P]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true]
      exact forall_congr' fun i => imp_congr (hiff i) Iff.rfl
    refine ⟨e, he, hiff, ?_⟩
    rw [hcard8] at hff
    have : Nat.card (fixV (B.map (g2OAct (ZMod 2)))) = cntO (sE8.getD e []) := by
      rw [hC, hfilter]
      rfl
    omega

end CFSG.Quasithin.H13.U3.GC137.S2
