
module

public import CFSG.Sporadic.J4.QT2LocX0CentMainBase
import all CFSG.Sporadic.J4.QT2LocX0CentMainBase

public import CFSG.Sporadic.J4.QT2LocX0KCheck

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix
open scoped Classical

set_option maxRecDepth 100000

private theorem k_facts :
    kWords.length = 6 ∧ kGenRows.size = 6 ∧ kInvRows.size = 6 ∧
    (∀ w ∈ kWords, ∀ l ∈ w, l ∈ letters) ∧
    (∀ i < 6, wfRows kGenRows[i]! = true ∧ wfRows kInvRows[i]! = true ∧
      eqRows (mulRows kGenRows[i]! kInvRows[i]!) idRows = true ∧
      eqRows (mulRows kInvRows[i]! kGenRows[i]!) idRows = true ∧
      (frApply (frTable kGenRows[i]!) x0Q1).beq x0Q1 = true) ∧
    x0Q1 ∈ x0Pts ∧ differs x0Q1 rootV = true := by
  have h := chkKGens_true
  unfold chkKGens at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, fun w hw l hl => by simpa using h4 w hw l hl, fun i hi => by
    obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h5 i hi
    exact ⟨a, b, c, d, e⟩, h6, h7⟩

private theorem kGenRows_get {i : ℕ} (hi : i < 6) :
    kGenRows[i]! = QT2A.wR (kWords.getD i []) := by
  obtain ⟨h1, -⟩ := k_facts
  have hi' : i < kWords.length := by omega
  unfold kGenRows
  simp [hi']

private theorem kAllRows_get_lt
    {i : ℕ} (hi : i < 6) : kAllRows[i]! = kGenRows[i]! := by
  obtain ⟨-, h2, -⟩ := k_facts
  have hi' : i < kGenRows.size := by omega
  rw [getElem!_pos kAllRows i (by simp [kAllRows, h2, kInvRows]; omega),
    getElem!_pos kGenRows i hi']
  unfold kAllRows
  exact Array.getElem_append_left hi'

private theorem kAllRows_get_ge {i : ℕ} (hi : 6 ≤ i) (hi2 : i < 12) :
    kAllRows[i]! = kInvRows[i - 6]! := by
  obtain ⟨-, h2, h3, -⟩ := k_facts
  have hi' : i - 6 < kInvRows.size := by omega
  rw [getElem!_pos kAllRows i (by simp [kAllRows, h2, kInvRows]; omega),
    getElem!_pos kInvRows (i - 6) hi']
  unfold kAllRows
  rw [Array.getElem_append_right (by omega)]
  congr 1

theorem Mx_kGen_lt (hM : MatFacts) {i : ℕ} (hi : i < 6) :
    Mx (kGen i) = rowsMatrix (kAllRows[i]!) := by
  rw [kAllRows_get_lt hi, kGenRows_get hi, kGen, ite_eq_left hi]
  exact QT2A.Mx_el5 hM _

theorem Mx_kGen (hM : MatFacts) {i : ℕ} (hi : i < 12) :
    Mx (kGen i) = rowsMatrix (kAllRows[i]!) := by
  by_cases h : i < 6
  · exact Mx_kGen_lt hM h
  · have h6 : 6 ≤ i := by omega
    obtain ⟨-, -, -, -, hf, -⟩ := k_facts
    obtain ⟨-, -, hc, hd, -⟩ := hf (i - 6) (by omega)
    have hg : Mx (kGen (i - 6)) = rowsMatrix (kGenRows[i - 6]!) := by
      have := Mx_kGen_lt hM (i := i - 6) (by omega)
      rwa [kAllRows_get_lt (by omega)] at this
    have hinv : kGen i = (kGen (i - 6))⁻¹ := by
      unfold kGen
      rw [ite_eq_right h, ite_eq_left (by omega)]
    rw [kAllRows_get_ge h6 hi, hinv]
    have e2 : rowsMatrix kInvRows[i - 6]! * rowsMatrix kGenRows[i - 6]! = 1 := by
      rw [← rowsMatrix_mulRows, eqRows_iff.1 hd, rowsMatrix_idRows]
    have e3 : Mx (kGen (i - 6)) * Mx (kGen (i - 6))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    calc Mx (kGen (i - 6))⁻¹ = (rowsMatrix kInvRows[i - 6]! * rowsMatrix kGenRows[i - 6]!) *
          Mx (kGen (i - 6))⁻¹ := by rw [e2, one_mul]
      _ = rowsMatrix kInvRows[i - 6]! * (Mx (kGen (i - 6)) * Mx (kGen (i - 6))⁻¹) := by
          rw [mul_assoc, ← hg]
      _ = rowsMatrix kInvRows[i - 6]! := by rw [e3, mul_one]

theorem kOrb_ok :
    oOrbOK (fun M g => mulRows M (kAllRows[g]!)) 12 idRows kOrb 15360 = true :=
  chkKOrb_true

theorem card_KSub (hM : MatFacts) : Nat.card KSub = 15360 :=
  card_enum (fun _ hi => Mx_kGen hM hi) kOrb_ok

theorem kGen_mem_Hj
    {i : ℕ} (hi : i < 12) : kGen i ∈ Hj := by
  obtain ⟨-, -, -, hl, -⟩ := k_facts
  have hw : ∀ j < 6, QT2A.el5 (kWords.getD j []) ∈ Hj := by
    intro j hj
    have hmem : kWords.getD j [] ∈ kWords := by
      obtain ⟨h1, -⟩ := k_facts
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    unfold QT2A.el5
    rw [wordProd_gen5_xJ _ (hl _ hmem)]
    exact wordProd_mem_Hj (hl _ hmem)
  unfold kGen
  by_cases h : i < 6
  · rw [ite_eq_left h]
    exact hw i h
  · rw [ite_eq_right h]
    exact Hj.inv_mem (hw (i - 6) (by omega))

theorem el5_inv_smul_q1 (hM : MatFacts) {i : ℕ} (hi : i < 6) :
    (QT2A.el5 (kWords.getD i []))⁻¹ • q1Row = q1Row := by
  obtain ⟨-, -, -, -, hf, -⟩ := k_facts
  obtain ⟨-, -, -, -, hq⟩ := hf i hi
  rw [← ofRow_inj, inv_smul_row, ← Mx_apply, QT2A.Mx_el5 hM, ← kGenRows_get hi, q1Row]
  show x0Q1.toVec ᵥ* rowsMatrix kGenRows[i]! = x0Q1.toVec
  rw [← frApply_toVec_eq_vecMul]
  exact congrArg V2.toVec (V2.beq_iff.1 hq)

theorem kGen_smul_q1
    (hM : MatFacts) {i : ℕ} (hi : i < 12) : kGen i • q1Row = q1Row := by
  unfold kGen
  by_cases h : i < 6
  · rw [ite_eq_left h]
    have := el5_inv_smul_q1 hM h
    rwa [inv_smul_eq_iff, eq_comm] at this
  · rw [ite_eq_right h]
    exact el5_inv_smul_q1 hM (by omega)

theorem KSub_le
    (hM : MatFacts) : KSub ≤ Hj ⊓ MulAction.stabilizer J q1Row := by
  rw [KSub, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨kGen_mem_Hj hi, kGen_smul_q1 hM hi⟩

theorem card_Estab_rep
    (hM : MatFacts) {ℓ : ℕ} (hℓ : ℓ < 7) :
    Nat.card ↥(Estab (rep ℓ)) = [2048, 2, 1, 1, 16, 512, 128].getD ℓ 0 := by
  rw [rep_toVec hM hℓ, card_Estab_toRow hM]
  have h := chkEStab_true
  unfold chkEStab at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact h.2 ℓ hℓ

theorem card_Estab_q1
    (hM : MatFacts) : Nat.card ↥(Estab q1Row) = 2 := by
  rw [q1Row, card_Estab_toRow hM]
  have h := chkEStab_true
  unfold chkEStab at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact h.1

theorem q1_mem_pts : q1Row ∈ x0PtSet := by
  obtain ⟨-, -, -, -, -, hq, -⟩ := k_facts
  unfold x0PtSet q1Row
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨x0Q1, List.mem_eraseDups.2 hq, rfl⟩

theorem q1_ne_w₀ : q1Row ≠ w₀ := by
  obtain ⟨-, -, -, -, -, -, hd⟩ := k_facts
  exact differs_toVec hd

private theorem kOrb_facts :
    kOrb.mats.size = 15360 ∧ 0 < 15360 ∧ kOrb.mats[0]! = idRows ∧
      ∀ q < 15360, oOrbAt (fun M g => mulRows M (kAllRows[g]!)) 12 kOrb q = true :=
  enum_facts kOrb_ok

private theorem kComm_len : (kOrb.mats.toList.filter fun M =>
    eqRows (mulRows M (x0GenRows[0]!)) (mulRows (x0GenRows[0]!) M)).length = 40 := by
  have h := chkKComm_true
  unfold chkKComm at h
  simpa using h

end CFSG.Sporadic.J4.QT2
