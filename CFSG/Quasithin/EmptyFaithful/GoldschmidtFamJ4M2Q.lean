module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2ExtraGen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gens
public import Certificates.Certificate4201

public section

namespace CFSG.Quasithin.J4M2

open scoped commutatorElement

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4Loc

@[expose] noncomputable def Qgrp : Subgroup J := Subgroup.closure {x | ∃ k < 12, x = gE k}

@[expose] noncomputable def B0grp : Subgroup J := Subgroup.closure {x | ∃ n < 17, x = gE n}

theorem Qgrp_eq_closure_range :
    Qgrp = Subgroup.closure (Set.range fun i : Fin 12 => gE i.val) := by
  unfold Qgrp
  congr 1
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.2, rfl⟩

theorem gE_mem_Qgrp {k : ℕ} (hk : k < 12) : gE k ∈ Qgrp :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem gE_mem_B0 {n : ℕ} (hn : n < 17) : gE n ∈ B0grp :=
  Subgroup.subset_closure ⟨n, hn, rfl⟩

theorem Qgrp_le_M2
    (hM : MatFacts) : Qgrp ≤ M2 := by
  rw [Qgrp, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact gE_mem_M2 hM (by omega)

theorem Qgrp_le_B0 : Qgrp ≤ B0grp := by
  rw [Qgrp, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact gE_mem_B0 (by omega)

theorem cE_mem_B0 : cE ∈ B0grp := by
  rw [cE, commutatorElement_def]
  have ha := gE_mem_B0 (n := 12) (by norm_num)
  have hb := gE_mem_B0 (n := 13) (by norm_num)
  exact B0grp.mul_mem (B0grp.mul_mem (B0grp.mul_mem ha hb) (B0grp.inv_mem ha)) (B0grp.inv_mem hb)

theorem cE_mem_commutator_B0 : cE ∈ ⁅B0grp, B0grp⁆ :=
  Subgroup.commutator_mem_commutator (gE_mem_B0 (n := 12) (by norm_num))
    (gE_mem_B0 (n := 13) (by norm_num))

theorem qM_size : qM.size = 12 := by
  unfold qM
  rw [List.size_toArray, List.length_map, List.length_range]

theorem qI_size : qI.size = 12 := by
  unfold qI
  rw [Array.size_map, qM_size]

theorem oI_size : oI.size = 5 := by
  unfold oI
  rw [List.size_toArray, List.length_map, List.length_range]

theorem qM_getElem {k : ℕ} (hk : k < 12) : qM[k]! = gmats[k]! := by
  have h : k < qM.size := by rw [qM_size]; exact hk
  rw [getElem!_pos qM k h]
  simp [qM]

theorem qT_getElem {k : ℕ} (hk : k < 12) : qT[k]! = frTable qM[k]! := by
  have h : k < qM.size := by rw [qM_size]; exact hk
  have h' : k < qT.size := by
    unfold qT
    rw [Array.size_map]
    exact h
  rw [getElem!_pos qT k h']
  simp [qT, getElem!_pos qM k h]

theorem qIT_getElem {k : ℕ} (hk : k < 12) : qIT[k]! = frTable qI[k]! := by
  have h : k < qI.size := by rw [qI_size]; exact hk
  have h' : k < qIT.size := by
    unfold qIT
    rw [Array.size_map]
    exact h
  rw [getElem!_pos qIT k h']
  simp [qIT, getElem!_pos qI k h]

theorem oIT_getElem {i : ℕ} (hi : i < 5) : oIT[i]! = frTable oI[i]! := by
  have h : i < oI.size := by rw [oI_size]; exact hi
  have h' : i < oIT.size := by
    unfold oIT
    rw [Array.size_map]
    exact h
  rw [getElem!_pos oIT i h']
  simp [oIT, getElem!_pos oI i h]

theorem bcols_getElem {j : ℕ} (hj : j < 12) : bcols[j]! = bcol j := by
  have h : j < bcols.size := by
    unfold bcols
    rw [List.size_toArray, List.length_map, List.length_range]
    exact hj
  rw [getElem!_pos bcols j h]
  simp [bcols]

theorem rowsMatrix_mulT_frTable (X Y : Array V2) :
    rowsMatrix (mulT X (frTable Y)) = rowsMatrix X * rowsMatrix Y := by
  rw [mulT_frTable, rowsMatrix_mulRows]

theorem rowsMatrix_mulT_qT (X : Array V2) {k : ℕ} (hk : k < 12) :
    rowsMatrix (mulT X qT[k]!) = rowsMatrix X * rowsMatrix qM[k]! := by
  rw [qT_getElem hk, rowsMatrix_mulT_frTable]

theorem rowsMatrix_mulT_qIT (X : Array V2) {k : ℕ} (hk : k < 12) :
    rowsMatrix (mulT X qIT[k]!) = rowsMatrix X * rowsMatrix qI[k]! := by
  rw [qIT_getElem hk, rowsMatrix_mulT_frTable]

theorem rowsMatrix_mulT_oIT (X : Array V2) {i : ℕ} (hi : i < 5) :
    rowsMatrix (mulT X oIT[i]!) = rowsMatrix X * rowsMatrix oI[i]! := by
  rw [oIT_getElem hi, rowsMatrix_mulT_frTable]

theorem rowsMatrix_mulT_gtabs (X : Array V2) {n : ℕ} (hn : n < 32) :
    rowsMatrix (mulT X gtabs[n]!) = rowsMatrix X * rowsMatrix gmats[n]! := by
  rw [gtabs_getElem hn, rowsMatrix_mulT_frTable]

theorem rowsMatrix_mulT_zT (X : Array V2) :
    rowsMatrix (mulT X zT) = rowsMatrix X * rowsMatrix zM :=
  rowsMatrix_mulT_frTable X zM

theorem Mx_q (hM : MatFacts) {k : ℕ} (hk : k < 12) : Mx (gE k) = rowsMatrix qM[k]! := by
  rw [Mx_gE hM (by omega), qM_getElem hk]

theorem chkQRel_parts :
    eqRows zComm zM = true ∧ wfR zM = true ∧ eqRows zM idRows = false ∧
      eqRows (mulT zM zT) idRows = true ∧
      (∀ k < 12, eqRows (mulT qM[k]! qIT[k]!) idRows = true) ∧
      (∀ k < 12, eqRows (mulT qM[k]! zT) (mulT zM qT[k]!) = true) ∧
      (∀ k < 12, eqRows (mulT qM[k]! qT[k]!) idRows = true ∨
        eqRows (mulT qM[k]! qT[k]!) zM = true) ∧
      (∀ i < 12, ∀ j < 12, eqRows (mulT qM[i]! qT[j]!) (mulT qM[j]! qT[i]!) = true ∨
        eqRows (mulT qM[i]! qT[j]!) (mulT (mulT qM[j]! qT[i]!) zT) = true) ∧
      chkNondeg = true := by
  have h := Certificates.certificate4201.1
  unfold chkQRel at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, fun k hk => (h5 k hk).1.1, fun k hk => (h5 k hk).1.2,
    fun k hk => (h5 k hk).2, h6, h7⟩

theorem chkQPerf_parts :
    (∀ i < 5, eqRows (mulT gmats[12 + i]! oIT[i]!) idRows = true) ∧
      ∀ k < 12, (∀ p ∈ perfData[k]!.1, 12 ≤ p.1 ∧ p.1 < 17 ∧ p.2 < 12) ∧
        eqRows (if perfData[k]!.2 then mulT (commProd perfData[k]!.1) zT
          else commProd perfData[k]!.1) qM[k]! = true := by
  have h := Certificates.certificate4201.2.2
  unfold chkQPerf at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun k hk => ⟨fun p hp => ?_, (h2 k hk).2⟩⟩
  have h3 := (h2 k hk).1 p hp
  exact ⟨h3.1.1, h3.1.2, h3.2⟩

theorem z0_mul_self (hM : MatFacts) : z0 * z0 = 1 :=
  eta_sq (elem_uJ hM) 1131

theorem z0_ne_one (hM : MatFacts) : z0 ≠ 1 := by
  intro h
  have h1 : eta uJ 11 1131 = eta uJ 11 0 := by
    rw [eta_zero]
    exact h
  have h2 := eta_inj' hM (by norm_num) (by norm_num) h1
  omega

theorem Mx_inv_q (hM : MatFacts) {k : ℕ} (hk : k < 12) :
    Mx (gE k)⁻¹ = rowsMatrix qI[k]! := by
  obtain ⟨-, -, -, -, hinv, -⟩ := chkQRel_parts
  have h := hinv k hk
  rw [qIT_getElem hk] at h
  exact rowsMatrix_inv_of_mul (Mx_q hM hk) h

theorem z0_eq_commutator
    (hM : MatFacts) : z0 = ⁅gE 0, gE 1⁆ := by
  obtain ⟨h1, -⟩ := chkQRel_parts
  have h2 := rowsMatrix_eq_of_eqRows h1
  unfold zComm at h2
  rw [rowsMatrix_mulT_qIT _ (by norm_num), rowsMatrix_mulT_qIT _ (by norm_num),
    rowsMatrix_mulT_qT _ (by norm_num)] at h2
  apply Mx_injective
  rw [rowsMatrix_zM hM] at h2
  rw [commutatorElement_def, map_mul, map_mul, map_mul, ← h2, Mx_q hM (by norm_num),
    Mx_q hM (by norm_num), Mx_inv_q hM (by norm_num), Mx_inv_q hM (by norm_num)]

theorem z0_mem_Qgrp
    (hM : MatFacts) : z0 ∈ Qgrp := by
  rw [z0_eq_commutator hM, commutatorElement_def]
  have h0 := gE_mem_Qgrp (k := 0) (by norm_num)
  have h1 := gE_mem_Qgrp (k := 1) (by norm_num)
  exact Qgrp.mul_mem (Qgrp.mul_mem (Qgrp.mul_mem h0 h1) (Qgrp.inv_mem h0)) (Qgrp.inv_mem h1)

theorem Qgens_comm_z0 (hM : MatFacts)
    {k : ℕ} (hk : k < 12) : z0 * gE k = gE k * z0 := by
  obtain ⟨-, -, -, -, -, hzc, -⟩ := chkQRel_parts
  have h := congrArg rowsMatrix (eqRows_iff.1 (hzc k hk))
  rw [rowsMatrix_mulT_zT, rowsMatrix_mulT_qT _ hk, ← Mx_q hM hk, rowsMatrix_zM hM] at h
  apply Mx_injective
  rw [map_mul, map_mul]
  exact h.symm

theorem Qgens_sq (hM : MatFacts)
    {k : ℕ} (hk : k < 12) : gE k * gE k = 1 ∨ gE k * gE k = z0 := by
  obtain ⟨-, -, -, -, -, -, hsq, -⟩ := chkQRel_parts
  rcases hsq k hk with h | h
  · left
    have h2 := congrArg rowsMatrix (eqRows_iff.1 h)
    rw [rowsMatrix_mulT_qT _ hk, rowsMatrix_idRows, ← Mx_q hM hk] at h2
    apply Mx_injective
    rw [map_mul, map_one]
    exact h2
  · right
    have h2 := congrArg rowsMatrix (eqRows_iff.1 h)
    rw [rowsMatrix_mulT_qT _ hk, ← Mx_q hM hk, rowsMatrix_zM hM] at h2
    apply Mx_injective
    rw [map_mul]
    exact h2

@[expose] def Qform (i j : Fin 12) : ZMod 2 := if qNC i.val j.val then 1 else 0

theorem Qgens_comm (hM : MatFacts)
    (i j : Fin 12) : gE i.val * gE j.val = gE j.val * gE i.val * z0 ^ (Qform i j).val := by
  obtain ⟨-, -, -, -, -, -, -, hcomm, -⟩ := chkQRel_parts
  have hi := i.2
  have hj := j.2
  have h1 : (1 : ZMod 2).val = 1 := rfl
  unfold Qform
  cases hq : qNC i.val j.val
  · have h2 : eqRows (mulT qM[i.val]! qT[j.val]!) (mulT qM[j.val]! qT[i.val]!) = true := by
      unfold qNC at hq
      simpa using hq
    have h3 := congrArg rowsMatrix (eqRows_iff.1 h2)
    rw [rowsMatrix_mulT_qT _ hj, rowsMatrix_mulT_qT _ hi, ← Mx_q hM hi, ← Mx_q hM hj] at h3
    apply Mx_injective
    simp only [Bool.false_eq_true, ↓reduceIte, ZMod.val_zero, pow_zero, mul_one]
    rw [map_mul, map_mul]
    exact h3
  · have h2 : eqRows (mulT qM[i.val]! qT[j.val]!) (mulT qM[j.val]! qT[i.val]!) = false := by
      unfold qNC at hq
      simpa using hq
    rcases hcomm i.val hi j.val hj with h | h
    · rw [h2] at h
      exact absurd h (by simp)
    · have h3 := congrArg rowsMatrix (eqRows_iff.1 h)
      rw [rowsMatrix_mulT_qT _ hj, rowsMatrix_mulT_zT, rowsMatrix_mulT_qT _ hi, ← Mx_q hM hi,
        ← Mx_q hM hj, rowsMatrix_zM hM] at h3
      apply Mx_injective
      simp only [eq_self, ite_true, h1, pow_one]
      rw [map_mul, map_mul, map_mul]
      exact h3

@[expose] def bitsOf (p : ℕ → Bool) (n : ℕ) : ℕ :=
  (List.range n).foldl (fun m i => if p i then m + 2 ^ i else m) 0

theorem bcol_eq_bitsOf (j : ℕ) : bcol j = bitsOf (fun i => qNC i j) 12 := rfl

theorem bitsOf_succ (p : ℕ → Bool) (n : ℕ) :
    bitsOf p (n + 1) = if p n then bitsOf p n + 2 ^ n else bitsOf p n := by
  unfold bitsOf
  rw [List.range_succ, List.foldl_append]
  by_cases h : p n <;> simp [h]

theorem bitsOf_lt (p : ℕ → Bool) (n : ℕ) : bitsOf p n < 2 ^ n := by
  induction n with
  | zero => simp [bitsOf]
  | succ n ih =>
    rw [bitsOf_succ, pow_succ]
    split_ifs <;> omega

theorem testBit_bitsOf (p : ℕ → Bool) (n : ℕ) {k : ℕ} (hk : k < n) :
    (bitsOf p n).testBit k = p k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [bitsOf_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
    · split_ifs
      · rw [add_comm, Nat.testBit_two_pow_add_gt hk', ih hk']
      · exact ih hk'
    · split_ifs with h
      · rw [add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (bitsOf_lt p k), h]
        rfl
      · rw [Nat.testBit_lt_two_pow (bitsOf_lt p k)]
        simpa using h

theorem foldl_bne_range (f : ℕ → Bool) (n : ℕ) :
    (if (List.range n).foldl (fun b i => b != f i) false then (1 : ZMod 2) else 0) =
      ∑ i ∈ Finset.range n, if f i then (1 : ZMod 2) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← ih]
    generalize (List.range n).foldl (fun b i => b != f i) false = b
    cases b <;> cases f n <;> decide

theorem nondeg_of_chkNondeg (h : chkNondeg = true) :
    ∀ e : Fin 12 → ZMod 2, (∀ j, ∑ i, e i * Qform i j = 0) → e = 0 := by
  intro e he
  have key : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
  let p : ℕ → Bool := fun i => if hi : i < 12 then decide (e ⟨i, hi⟩ = 1) else false
  have hbit : ∀ i : Fin 12, (bitsOf p 12).testBit i.val = decide (e i = 1) := by
    intro i
    rw [testBit_bitsOf p 12 i.2]
    simp [p]
  have hlt : bitsOf p 12 < 4096 := by
    have h1 := bitsOf_lt p 12
    norm_num at h1
    exact h1
  unfold chkNondeg at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true] at h
  rcases h (bitsOf p 12) hlt with h0 | ⟨j, hj, hpar⟩
  · funext i
    have h1 := hbit i
    rw [h0, Nat.zero_testBit] at h1
    rcases key (e i) with h2 | h2
    · exact h2
    · rw [h2] at h1
      exact absurd h1 (by simp)
  · exfalso
    have hpar' : parity12 (bitsOf p 12 &&& bcol j) = true := by rwa [bcols_getElem hj] at hpar
    have h3 : (if parity12 (bitsOf p 12 &&& bcol j) then (1 : ZMod 2) else 0) =
        ∑ i : Fin 12, e i * Qform i ⟨j, hj⟩ := by
      calc (if parity12 (bitsOf p 12 &&& bcol j) then (1 : ZMod 2) else 0)
          = ∑ i ∈ Finset.range 12, if (bitsOf p 12 &&& bcol j).testBit i then (1 : ZMod 2) else 0 :=
            foldl_bne_range (fun i => (bitsOf p 12 &&& bcol j).testBit i) 12
        _ = ∑ i : Fin 12, if (bitsOf p 12 &&& bcol j).testBit i.val then (1 : ZMod 2) else 0 :=
            (Fin.sum_univ_eq_sum_range
              (fun i => if (bitsOf p 12 &&& bcol j).testBit i then (1 : ZMod 2) else 0) 12).symm
        _ = ∑ i : Fin 12, e i * Qform i ⟨j, hj⟩ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Nat.testBit_and, hbit i, bcol_eq_bitsOf, testBit_bitsOf _ 12 i.2]
            unfold Qform
            rcases key (e i) with h0 | h0 <;> cases qNC i.val j <;> simp [h0]
    rw [hpar', he ⟨j, hj⟩] at h3
    exact absurd h3 (by decide)

theorem chkNondeg_true : chkNondeg = true := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := chkQRel_parts
  exact h

theorem Qgrp_main (hM : MatFacts) :
    Nat.card Qgrp = 2 ^ 13 ∧ CFSG.IsExtraspecialPGroup 2 ↥Qgrp ∧
      ∀ x ∈ Qgrp, (∀ y ∈ Qgrp, x * y = y * x) → x ∈ Subgroup.zpowers z0 := by
  have h := card_and_extraspecial_of_gens (fun i : Fin 12 => gE i.val) z0 (z0_ne_one hM)
    (z0_mul_self hM) (by rw [← Qgrp_eq_closure_range]; exact z0_mem_Qgrp hM)
    (fun i => Qgens_comm_z0 hM i.2) Qform (fun i => Qgens_sq hM i.2) (Qgens_comm hM)
    (nondeg_of_chkNondeg chkNondeg_true)
  rw [← Qgrp_eq_closure_range] at h
  exact h

theorem card_Qgrp
    (hM : MatFacts) : Nat.card Qgrp = 2 ^ 13 :=
  (Qgrp_main hM).1

theorem isExtraspecial_Qgrp
    (hM : MatFacts) : CFSG.IsExtraspecialPGroup 2 ↥Qgrp :=
  (Qgrp_main hM).2.1

theorem center_Qgrp
    (hM : MatFacts) : ∀ x ∈ Qgrp, (∀ y ∈ Qgrp, x * y = y * x) → x ∈ Subgroup.zpowers z0 :=
  (Qgrp_main hM).2.2

theorem isPGroup_Qgrp
    (hM : MatFacts) : IsPGroup 2 ↥Qgrp :=
  IsPGroup.of_card (card_Qgrp hM)

theorem conj_mem_of_closure {G : Type*} [Group G] (c : G) (H : Subgroup G) (S : Set G)
    (hS : ∀ s ∈ S, c * s * c⁻¹ ∈ H) : ∀ x ∈ Subgroup.closure S, c * x * c⁻¹ ∈ H := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hS y hy
  | one => simp
  | mul y w _ _ hy hw =>
    have h : c * (y * w) * c⁻¹ = (c * y * c⁻¹) * (c * w * c⁻¹) := by group
    rw [h]
    exact H.mul_mem hy hw
  | inv y _ hy =>
    have h : c * y⁻¹ * c⁻¹ = (c * y * c⁻¹)⁻¹ := by group
    rw [h]
    exact H.inv_mem hy

theorem exists_mem_Qgrp_qProd
    (hM : MatFacts) (e : ℕ) (δ : Bool) : ∃ y ∈ Qgrp, Mx y = rowsMatrix (qProd e δ) := by
  have hfold : ∀ (l : List ℕ), (∀ j ∈ l, j < 12) → ∀ (acc : Array V2),
      (∃ y ∈ Qgrp, Mx y = rowsMatrix acc) →
      ∃ y ∈ Qgrp, Mx y = rowsMatrix (l.foldl
        (fun acc j => if e.testBit j then mulT acc qT[j]! else acc) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons j l ih =>
      intro hl acc hacc
      have hj : j < 12 := hl j List.mem_cons_self
      rw [List.foldl_cons]
      refine ih (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')) _ ?_
      by_cases hb : e.testBit j
      · rw [ite_eq_left hb]
        obtain ⟨y, hy, hyM⟩ := hacc
        refine ⟨y * gE j, Qgrp.mul_mem hy (gE_mem_Qgrp hj), ?_⟩
        rw [map_mul, hyM, Mx_q hM hj, rowsMatrix_mulT_qT _ hj]
      · rw [ite_eq_right hb]
        exact hacc
  have hm := hfold (List.range 12) (fun j hj => List.mem_range.1 hj) idRows
    ⟨1, Qgrp.one_mem, by rw [map_one, rowsMatrix_idRows]⟩
  have e1 : qProd e δ = if δ then mulT ((List.range 12).foldl
      (fun acc j => if e.testBit j then mulT acc qT[j]! else acc) idRows) zT
      else (List.range 12).foldl (fun acc j => if e.testBit j then mulT acc qT[j]! else acc)
        idRows := rfl
  rw [e1]
  by_cases hδ : δ = true
  · rw [ite_eq_left hδ]
    obtain ⟨y, hy, hyM⟩ := hm
    refine ⟨y * z0, Qgrp.mul_mem hy (z0_mem_Qgrp hM), ?_⟩
    rw [map_mul, hyM, rowsMatrix_mulT_zT, rowsMatrix_zM hM]
  · rw [ite_eq_right hδ]
    exact hm

theorem cE_normalizes_Qgrp
    (hM : MatFacts) : ∀ x ∈ Qgrp, cE * x * cE⁻¹ ∈ Qgrp := by
  have hc := Certificates.certificate4201.2.1
  unfold chkQC at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨h1, h2⟩ := hc
  have hci : Mx cE⁻¹ = rowsMatrix (invRows cMat) := rowsMatrix_inv_of_mul (Mx_cE hM) h1
  refine conj_mem_of_closure cE Qgrp _ ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨y, hy, hyM⟩ := exists_mem_Qgrp_qProd hM cNormData[k]!.1 cNormData[k]!.2
  have h3 := congrArg rowsMatrix (eqRows_iff.1 (h2 k hk))
  rw [rowsMatrix_mulT_frTable, rowsMatrix_mulT_qT _ hk, ← Mx_cE hM, ← Mx_q hM hk, ← hci,
    ← hyM] at h3
  have h4 : cE * gE k * cE⁻¹ = y := by
    apply Mx_injective
    rw [map_mul, map_mul]
    exact h3
  rw [h4]
  exact hy

theorem Mx_inv_o (hM : MatFacts) {i : ℕ} (hi : i < 5) :
    Mx (gE (12 + i))⁻¹ = rowsMatrix oI[i]! := by
  obtain ⟨hinv, -⟩ := chkQPerf_parts
  have h := hinv i hi
  rw [oIT_getElem hi] at h
  exact rowsMatrix_inv_of_mul (Mx_gE hM (by omega)) h

theorem Mx_commStep (hM : MatFacts) {p : ℕ × ℕ} (hp1 : 12 ≤ p.1)
    (hp2 : p.1 < 17) (hp3 : p.2 < 12) (acc : Array V2) (x : J) (hx : Mx x = rowsMatrix acc) :
    Mx (x * ⁅gE p.1, gE p.2⁆) =
      rowsMatrix (mulT (mulT (mulT (mulT acc gtabs[p.1]!) qT[p.2]!) oIT[p.1 - 12]!)
        qIT[p.2]!) := by
  have hg : Mx (gE p.1)⁻¹ = rowsMatrix oI[p.1 - 12]! := by
    have h := Mx_inv_o hM (i := p.1 - 12) (by omega)
    rwa [show 12 + (p.1 - 12) = p.1 by omega] at h
  rw [rowsMatrix_mulT_qIT _ hp3, rowsMatrix_mulT_oIT _ (by omega), rowsMatrix_mulT_qT _ hp3,
    rowsMatrix_mulT_gtabs _ (by omega), ← hx, ← Mx_gE hM (by omega), ← hg, ← Mx_q hM hp3,
    ← Mx_inv_q hM hp3, commutatorElement_def]
  simp only [map_mul, mul_assoc]

theorem Mx_commFold (hM : MatFacts) :
    ∀ (l : List (ℕ × ℕ)), (∀ p ∈ l, 12 ≤ p.1 ∧ p.1 < 17 ∧ p.2 < 12) →
      ∀ (acc : Array V2) (x : J), Mx x = rowsMatrix acc →
        Mx (x * (l.map fun p => ⁅gE p.1, gE p.2⁆).prod) =
          rowsMatrix (l.foldl (fun acc p => mulT (mulT (mulT (mulT acc gtabs[p.1]!) qT[p.2]!)
            oIT[p.1 - 12]!) qIT[p.2]!) acc) := by
  intro l
  induction l with
  | nil =>
    intro _ acc x hx
    simpa using hx
  | cons p l ih =>
    intro hl acc x hx
    rw [List.map_cons, List.prod_cons, ← mul_assoc, List.foldl_cons]
    have hp := hl p List.mem_cons_self
    exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ _
      (Mx_commStep hM hp.1 hp.2.1 hp.2.2 acc x hx)

theorem Mx_commProd (hM : MatFacts) {l : List (ℕ × ℕ)}
    (hl : ∀ p ∈ l, 12 ≤ p.1 ∧ p.1 < 17 ∧ p.2 < 12) :
    Mx (l.map fun p => ⁅gE p.1, gE p.2⁆).prod = rowsMatrix (commProd l) := by
  have h := Mx_commFold hM l hl idRows 1 (by rw [map_one, rowsMatrix_idRows])
  rwa [one_mul] at h

theorem gE_mem_commutator_B0
    (hM : MatFacts) {k : ℕ} (hk : k < 12) : gE k ∈ ⁅B0grp, B0grp⁆ := by
  obtain ⟨-, hperf⟩ := chkQPerf_parts
  obtain ⟨hl, heq⟩ := hperf k hk
  have hprod : (perfData[k]!.1.map fun p => ⁅gE p.1, gE p.2⁆).prod ∈ ⁅B0grp, B0grp⁆ := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, h2, h3⟩ := hl p hp
    exact Subgroup.commutator_mem_commutator (gE_mem_B0 h2) (gE_mem_B0 (by omega))
  have hz : z0 ∈ ⁅B0grp, B0grp⁆ := by
    rw [z0_eq_commutator hM]
    exact Subgroup.commutator_mem_commutator (gE_mem_B0 (n := 0) (by norm_num))
      (gE_mem_B0 (n := 1) (by norm_num))
  have hm := Mx_commProd hM hl
  have h2 := congrArg rowsMatrix (eqRows_iff.1 heq)
  by_cases hδ : perfData[k]!.2 = true
  · rw [ite_eq_left hδ, rowsMatrix_mulT_zT, ← hm, rowsMatrix_zM hM, ← Mx_q hM hk] at h2
    have h3 : gE k = (perfData[k]!.1.map fun p => ⁅gE p.1, gE p.2⁆).prod * z0 := by
      apply Mx_injective
      rw [map_mul]
      exact h2.symm
    rw [h3]
    exact ⁅B0grp, B0grp⁆.mul_mem hprod hz
  · rw [ite_eq_right hδ, ← hm, ← Mx_q hM hk] at h2
    have h3 : gE k = (perfData[k]!.1.map fun p => ⁅gE p.1, gE p.2⁆).prod :=
      Mx_injective h2.symm
    rw [h3]
    exact hprod

theorem Qgrp_le_commutator_B0
    (hM : MatFacts) : Qgrp ≤ ⁅B0grp, B0grp⁆ := by
  rw [Qgrp, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact gE_mem_commutator_B0 hM hk

end CFSG.Quasithin.J4M2
