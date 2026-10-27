module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2R

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat

@[expose] def cntQ (l : List ℕ) : ℕ :=
  (o0Codes.filter fun c => !c.testBit 0 && l.all fun i => fixQB (sM i) c).length

@[expose] def cntO (l : List ℕ) : ℕ :=
  (o0Codes.filter fun c => l.all fun i => fixOB (sM i) c).length

theorem cntQ_A : cntQ Alist = 8 := by
  decide +kernel

theorem cntO_A : cntO Alist = 16 := by
  decide +kernel

theorem subA_Q : ∀ l ∈ Alist.sublists, l.length * cntQ l ≤ 8 * cntQ Alist := by
  decide +kernel

theorem subA_O : ∀ l ∈ Alist.sublists, l.length * cntO l ≤ 8 * cntO Alist := by
  decide +kernel

open Classical in
noncomputable def lst (B : Subgroup Gam) : List ℕ := Alist.filter fun i => decide (i ∈ idx B)

theorem mem_lst {B : Subgroup Gam} (hB : B ≤ Asub) {i : ℕ} : i ∈ lst B ↔ i ∈ idx B := by
  classical
  unfold lst
  rw [List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨hi, hmem⟩ := mem_idx.1 h
    obtain ⟨j, hj, hij⟩ := hB hmem
    rwa [sEltG_injective hi (A_lt j hj) hij]

theorem lst_sublist (B : Subgroup Gam) : lst B ∈ Alist.sublists := by
  classical
  exact List.mem_sublists.2 (List.filter_sublist)

theorem length_lst {B : Subgroup Gam} (hB : B ≤ Asub) : (lst B).length = (idx B).card := by
  classical
  have hnd : (lst B).Nodup := by
    unfold lst
    exact (by decide : Alist.Nodup).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext i
  rw [List.mem_toFinset, mem_lst hB]

theorem card_lst {B : Subgroup Gam} (hB : B ≤ Asub) : Nat.card B = (lst B).length := by
  rw [length_lst hB]
  exact card_eq_idx (hB.trans Asub_le_S)

theorem card_fixV_Q_lst {B : Subgroup Gam} (hB : B ≤ Asub) :
    Nat.card (fixV (B.map (g2QAct (ZMod 2)))) = cntQ (lst B) := by
  classical
  have := card_fixV_Q (hB.trans Asub_le_S) (fun c => (lst B).all fun i => fixQB (sM i) c)
    (fun c => by
      rw [List.all_eq_true]
      exact forall_congr' fun i => by rw [mem_lst hB])
  exact this

theorem card_fixV_O_lst {B : Subgroup Gam} (hB : B ≤ Asub) :
    Nat.card (fixV (B.map (g2OAct (ZMod 2)))) = cntO (lst B) := by
  classical
  have := card_fixV_O (hB.trans Asub_le_S) (fun c => (lst B).all fun i => fixOB (sM i) c)
    (fun c => by
      rw [List.all_eq_true]
      exact forall_congr' fun i => by rw [mem_lst hB])
  exact this

theorem lst_Asub : lst Asub = Alist := by
  classical
  unfold lst
  rw [List.filter_eq_self]
  intro i hi
  simpa using mem_idx_Asub.2 hi

end CFSG.Quasithin.H13.U3.GC137.S2
