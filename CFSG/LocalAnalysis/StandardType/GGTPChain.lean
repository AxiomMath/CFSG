module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeFin
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeTab
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CFSG.LocalAnalysis.StandardType.GGTPChainK
import CFSG.LocalAnalysis.StandardType.GGTPChainClosureK

public section

namespace CFSG.StandardType

open E6Dep

private def ggTP_ofMask (m : ℕ) : Finset ℕ :=
  (Finset.range 36).filter (fun i => m.testBit i = true)

private theorem ggTP_mem_ofMask (m i : ℕ) :
    i ∈ ggTP_ofMask m ↔ i < 36 ∧ m.testBit i = true := by
  simp [ggTP_ofMask, Finset.mem_filter, Finset.mem_range]

private theorem ggTP_ofMask_subset_of_and {m n : ℕ} (h : m &&& n = m) :
    ggTP_ofMask m ⊆ ggTP_ofMask n := by
  intro x hx
  rw [ggTP_mem_ofMask] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have hh := congrArg (fun k => k.testBit x) h
  rw [Nat.testBit_and] at hh
  rw [hx.2] at hh
  simpa using hh

private def ggTP_intervals (a0 a1 a2 a3 a4 : ℕ) : Finset ℕ :=
  {a0,
   cjN a0 a1,
   cjN a0 (cjN a1 a2),
   cjN a0 (cjN a1 (cjN a2 a3)),
   cjN a0 (cjN a1 (cjN a2 (cjN a3 a4))),
   a1,
   cjN a1 a2,
   cjN a1 (cjN a2 a3),
   cjN a1 (cjN a2 (cjN a3 a4)),
   a2,
   cjN a2 a3,
   cjN a2 (cjN a3 a4),
   a3,
   cjN a3 a4,
   a4}

private def ggTP_intervalsMask (a0 a1 a2 a3 a4 : ℕ) : ℕ :=
  2 ^ a0 |||
  2 ^ (cjN a0 a1) |||
  2 ^ (cjN a0 (cjN a1 a2)) |||
  2 ^ (cjN a0 (cjN a1 (cjN a2 a3))) |||
  2 ^ (cjN a0 (cjN a1 (cjN a2 (cjN a3 a4)))) |||
  2 ^ a1 |||
  2 ^ (cjN a1 a2) |||
  2 ^ (cjN a1 (cjN a2 a3)) |||
  2 ^ (cjN a1 (cjN a2 (cjN a3 a4))) |||
  2 ^ a2 |||
  2 ^ (cjN a2 a3) |||
  2 ^ (cjN a2 (cjN a3 a4)) |||
  2 ^ a3 |||
  2 ^ (cjN a3 a4) |||
  2 ^ a4

private theorem ggTP_ofMask_intervalsMask_subset (a0 a1 a2 a3 a4 : ℕ) :
    ggTP_ofMask (ggTP_intervalsMask a0 a1 a2 a3 a4) ⊆ ggTP_intervals a0 a1 a2 a3 a4 := by
  intro x hx
  rw [ggTP_mem_ofMask] at hx
  simp only [ggTP_intervalsMask, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq] at hx
  simpa only [ggTP_intervals, Finset.mem_insert, Finset.mem_singleton, eq_comm, or_assoc] using hx.2

private theorem ggTP_intervals_subset {a0 a1 a2 a3 a4 : ℕ} {J : Finset ℕ} (hJ : CjClosed J)
    (h0 : a0 ∈ J) (h1 : a1 ∈ J) (h2 : a2 ∈ J) (h3 : a3 ∈ J) (h4 : a4 ∈ J) :
    ggTP_intervals a0 a1 a2 a3 a4 ⊆ J := by
  intro x hx
  simp only [ggTP_intervals, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals repeat (first | apply hJ | assumption)

private def ggTP_rC : List ℕ :=
  [1, 0, 0, 1, 0, 0, 3, 3, 6, 1, 0, 0, 0, 0, 1, 16, 3, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1,
   0, 0, 0, 0, 1]

private def ggTP_r (c : ℕ) : ℕ := ggTP_rC.getD c 0

private def ggTP_fixMask : List ℕ :=
  [35593372616, 13458184672, 19668379088, 35592387841, 19674225412, 13469280002, 8455974919,
   60247215623, 16744511, 27087122609, 45421220012, 56458010778, 12250023514, 23292054124,
   41632959601, 32767, 61083746759, 7635468743, 41043510065, 12444637466, 22877971756, 56272165146,
   45836215596, 27667284785, 32356584585, 55301248674, 48591940244, 32235663945, 48397112404,
   54807586914, 35275813449, 17906422868, 9080039522, 4794685090, 2880514708, 1986350217]

private def ggTP_fixMaskOf (c : ℕ) : ℕ := ggTP_fixMask.getD c 0

private abbrev ggTP_pre1 (a0 a1 : ℕ) : Prop := a0 ≠ a1 ∧ cjN a0 a1 ≠ a1

private abbrev ggTP_pre2 (a0 a1 a2 : ℕ) : Prop :=
  ggTP_pre1 a0 a1 ∧ a1 ≠ a2 ∧ cjN a1 a2 ≠ a2 ∧ cjN a0 a2 = a2

private abbrev ggTP_pre3 (a0 a1 a2 a3 : ℕ) : Prop :=
  ggTP_pre2 a0 a1 a2 ∧ a2 ≠ a3 ∧ cjN a2 a3 ≠ a3 ∧ cjN a0 a3 = a3 ∧ cjN a1 a3 = a3

private abbrev ggTP_pre4 (a0 a1 a2 a3 a4 : ℕ) : Prop :=
  ggTP_pre3 a0 a1 a2 a3 ∧ a3 ≠ a4 ∧ cjN a3 a4 ≠ a4 ∧ cjN a0 a4 = a4 ∧ cjN a1 a4 = a4 ∧
    cjN a2 a4 = a4

private abbrev ggTP_valid (a0 a1 a2 a3 a4 : ℕ) : Prop := ggTP_pre4 a0 a1 a2 a3 a4

private def ggTP_findC (a0 a1 a2 a3 a4 : ℕ) : ℕ :=
  let m := ggTP_fixMaskOf a0 &&& ggTP_fixMaskOf a1 &&& ggTP_fixMaskOf a2 &&& ggTP_fixMaskOf a3 &&&
    ggTP_fixMaskOf a4
  ((List.range 36).find? (fun c => m.testBit c)).getD 0

private abbrev ggTP_good (a0 a1 a2 a3 a4 c : ℕ) : Prop :=
  c < 36 ∧ (a0 ≠ c ∧ cjN a0 c = c) ∧ (a1 ≠ c ∧ cjN a1 c = c) ∧ (a2 ≠ c ∧ cjN a2 c = c) ∧
  (a3 ≠ c ∧ cjN a3 c = c) ∧ (a4 ≠ c ∧ cjN a4 c = c) ∧
  ggTP_r c ≠ c ∧ cjN (ggTP_r c) c ≠ c ∧
  (ggTP_fixMaskOf c &&& ggTP_intervalsMask a0 a1 a2 a3 a4) = ggTP_fixMaskOf c

private def ggTP_rK (c : ℕ) : ℕ :=
  Bool.rec (ggTP_r c) (Nat.land (Nat.shiftRight GGTPK.rP (Nat.mul 6 c)) 63) (Nat.blt c 36)

private def ggTP_fixK (c : ℕ) : ℕ :=
  Bool.rec (ggTP_fixMaskOf c) (Nat.land (Nat.shiftRight GGTPK.fixP (Nat.mul 36 c)) 68719476735)
    (Nat.blt c 36)

private theorem ggTP_rK_chk :
    GGTPK.allK 36 (fun c => Nat.beq (Nat.land (Nat.shiftRight GGTPK.rP (Nat.mul 6 c)) 63)
      (ggTP_r c)) = true := by
  decide +kernel

private theorem ggTP_fixK_chk :
    GGTPK.allK 36 (fun c => Nat.beq (Nat.land (Nat.shiftRight GGTPK.fixP (Nat.mul 36 c))
      68719476735) (ggTP_fixMaskOf c)) = true := by
  decide +kernel

private theorem ggTP_r_eq (c : ℕ) : ggTP_r c = ggTP_rK c := by
  unfold ggTP_rK
  cases hc : Nat.blt c 36
  · rfl
  · exact (Nat.eq_of_beq_eq_true (GGTPK.allK_spec ggTP_rK_chk c (Nat.le_of_ble_eq_true hc))).symm

private theorem ggTP_fix_eq (c : ℕ) : ggTP_fixMaskOf c = ggTP_fixK c := by
  unfold ggTP_fixK
  cases hc : Nat.blt c 36
  · rfl
  · exact (Nat.eq_of_beq_eq_true (GGTPK.allK_spec ggTP_fixK_chk c (Nat.le_of_ble_eq_true hc))).symm

private def ggTP_intervalsMaskK (a0 a1 a2 a3 a4 : ℕ) : ℕ :=
  2 ^ a0 |||
  2 ^ (GGTPK.cjK a0 a1) |||
  2 ^ (GGTPK.cjK a0 (GGTPK.cjK a1 a2)) |||
  2 ^ (GGTPK.cjK a0 (GGTPK.cjK a1 (GGTPK.cjK a2 a3))) |||
  2 ^ (GGTPK.cjK a0 (GGTPK.cjK a1 (GGTPK.cjK a2 (GGTPK.cjK a3 a4)))) |||
  2 ^ a1 |||
  2 ^ (GGTPK.cjK a1 a2) |||
  2 ^ (GGTPK.cjK a1 (GGTPK.cjK a2 a3)) |||
  2 ^ (GGTPK.cjK a1 (GGTPK.cjK a2 (GGTPK.cjK a3 a4))) |||
  2 ^ a2 |||
  2 ^ (GGTPK.cjK a2 a3) |||
  2 ^ (GGTPK.cjK a2 (GGTPK.cjK a3 a4)) |||
  2 ^ a3 |||
  2 ^ (GGTPK.cjK a3 a4) |||
  2 ^ a4

private def ggTP_findCK (a0 a1 a2 a3 a4 : ℕ) : ℕ :=
  let m := ggTP_fixK a0 &&& ggTP_fixK a1 &&& ggTP_fixK a2 &&& ggTP_fixK a3 &&& ggTP_fixK a4
  ((List.range 36).find? (fun c => m.testBit c)).getD 0

private abbrev ggTP_goodK (a0 a1 a2 a3 a4 c : ℕ) : Prop :=
  c < 36 ∧ (a0 ≠ c ∧ GGTPK.cjK a0 c = c) ∧ (a1 ≠ c ∧ GGTPK.cjK a1 c = c) ∧
  (a2 ≠ c ∧ GGTPK.cjK a2 c = c) ∧ (a3 ≠ c ∧ GGTPK.cjK a3 c = c) ∧
  (a4 ≠ c ∧ GGTPK.cjK a4 c = c) ∧
  ggTP_rK c ≠ c ∧ GGTPK.cjK (ggTP_rK c) c ≠ c ∧
  (ggTP_fixK c &&& ggTP_intervalsMaskK a0 a1 a2 a3 a4) = ggTP_fixK c

private theorem ggTP_good_eq (a0 a1 a2 a3 a4 c : ℕ) :
    ggTP_good a0 a1 a2 a3 a4 c = ggTP_goodK a0 a1 a2 a3 a4 c := by
  simp only [ggTP_good, ggTP_goodK, ggTP_intervalsMask, ggTP_intervalsMaskK, GGTPK.cjN_eq_cjK,
    ggTP_r_eq, ggTP_fix_eq]

private theorem ggTP_findC_eq (a0 a1 a2 a3 a4 : ℕ) :
    ggTP_findC a0 a1 a2 a3 a4 = ggTP_findCK a0 a1 a2 a3 a4 := by
  simp only [ggTP_findC, ggTP_findCK, ggTP_fix_eq]

private def ggTP_leafK (a0 a1 a2 a3 a4 : ℕ) : Bool :=
  decide (ggTP_goodK a0 a1 a2 a3 a4 (ggTP_findCK a0 a1 a2 a3 a4))

private theorem ggTP_finK_0 : GGTPK.finK ggTP_leafK (0) = true := by decide +kernel
private theorem ggTP_finK_1 : GGTPK.finK ggTP_leafK (1) = true := by decide +kernel
private theorem ggTP_finK_2 : GGTPK.finK ggTP_leafK (2) = true := by decide +kernel
private theorem ggTP_finK_3 : GGTPK.finK ggTP_leafK (3) = true := by decide +kernel
private theorem ggTP_finK_4 : GGTPK.finK ggTP_leafK (4) = true := by decide +kernel
private theorem ggTP_finK_5 : GGTPK.finK ggTP_leafK (5) = true := by decide +kernel
private theorem ggTP_finK_6 : GGTPK.finK ggTP_leafK (6) = true := by decide +kernel
private theorem ggTP_finK_7 : GGTPK.finK ggTP_leafK (7) = true := by decide +kernel
private theorem ggTP_finK_8 : GGTPK.finK ggTP_leafK (8) = true := by decide +kernel
private theorem ggTP_finK_9 : GGTPK.finK ggTP_leafK (9) = true := by decide +kernel
private theorem ggTP_finK_10 : GGTPK.finK ggTP_leafK (10) = true := by decide +kernel
private theorem ggTP_finK_11 : GGTPK.finK ggTP_leafK (11) = true := by decide +kernel
private theorem ggTP_finK_12 : GGTPK.finK ggTP_leafK (12) = true := by decide +kernel
private theorem ggTP_finK_13 : GGTPK.finK ggTP_leafK (13) = true := by decide +kernel
private theorem ggTP_finK_14 : GGTPK.finK ggTP_leafK (14) = true := by decide +kernel
private theorem ggTP_finK_15 : GGTPK.finK ggTP_leafK (15) = true := by decide +kernel
private theorem ggTP_finK_16 : GGTPK.finK ggTP_leafK (16) = true := by decide +kernel
private theorem ggTP_finK_17 : GGTPK.finK ggTP_leafK (17) = true := by decide +kernel
private theorem ggTP_finK_18 : GGTPK.finK ggTP_leafK (18) = true := by decide +kernel
private theorem ggTP_finK_19 : GGTPK.finK ggTP_leafK (19) = true := by decide +kernel
private theorem ggTP_finK_20 : GGTPK.finK ggTP_leafK (20) = true := by decide +kernel
private theorem ggTP_finK_21 : GGTPK.finK ggTP_leafK (21) = true := by decide +kernel
private theorem ggTP_finK_22 : GGTPK.finK ggTP_leafK (22) = true := by decide +kernel
private theorem ggTP_finK_23 : GGTPK.finK ggTP_leafK (23) = true := by decide +kernel
private theorem ggTP_finK_24 : GGTPK.finK ggTP_leafK (24) = true := by decide +kernel
private theorem ggTP_finK_25 : GGTPK.finK ggTP_leafK (25) = true := by decide +kernel
private theorem ggTP_finK_26 : GGTPK.finK ggTP_leafK (26) = true := by decide +kernel
private theorem ggTP_finK_27 : GGTPK.finK ggTP_leafK (27) = true := by decide +kernel
private theorem ggTP_finK_28 : GGTPK.finK ggTP_leafK (28) = true := by decide +kernel
private theorem ggTP_finK_29 : GGTPK.finK ggTP_leafK (29) = true := by decide +kernel
private theorem ggTP_finK_30 : GGTPK.finK ggTP_leafK (30) = true := by decide +kernel
private theorem ggTP_finK_31 : GGTPK.finK ggTP_leafK (31) = true := by decide +kernel
private theorem ggTP_finK_32 : GGTPK.finK ggTP_leafK (32) = true := by decide +kernel
private theorem ggTP_finK_33 : GGTPK.finK ggTP_leafK (33) = true := by decide +kernel
private theorem ggTP_finK_34 : GGTPK.finK ggTP_leafK (34) = true := by decide +kernel
private theorem ggTP_finK_35 : GGTPK.finK ggTP_leafK (35) = true := by decide +kernel

private theorem ggTP_finK_true : ∀ a0 : Fin 36, GGTPK.finK ggTP_leafK a0 = true := by
  intro a0
  fin_cases a0
  · exact ggTP_finK_0
  · exact ggTP_finK_1
  · exact ggTP_finK_2
  · exact ggTP_finK_3
  · exact ggTP_finK_4
  · exact ggTP_finK_5
  · exact ggTP_finK_6
  · exact ggTP_finK_7
  · exact ggTP_finK_8
  · exact ggTP_finK_9
  · exact ggTP_finK_10
  · exact ggTP_finK_11
  · exact ggTP_finK_12
  · exact ggTP_finK_13
  · exact ggTP_finK_14
  · exact ggTP_finK_15
  · exact ggTP_finK_16
  · exact ggTP_finK_17
  · exact ggTP_finK_18
  · exact ggTP_finK_19
  · exact ggTP_finK_20
  · exact ggTP_finK_21
  · exact ggTP_finK_22
  · exact ggTP_finK_23
  · exact ggTP_finK_24
  · exact ggTP_finK_25
  · exact ggTP_finK_26
  · exact ggTP_finK_27
  · exact ggTP_finK_28
  · exact ggTP_finK_29
  · exact ggTP_finK_30
  · exact ggTP_finK_31
  · exact ggTP_finK_32
  · exact ggTP_finK_33
  · exact ggTP_finK_34
  · exact ggTP_finK_35

private theorem ggTP_finite :
    ∀ a0 a1 a2 a3 a4 : Fin 36, ggTP_valid a0 a1 a2 a3 a4 →
      ggTP_good a0 a1 a2 a3 a4 (ggTP_findC a0 a1 a2 a3 a4) := by
  intro a0 a1 a2 a3 a4 hv
  have h := GGTPK.finK_sound ggTP_leafK (a0 : ℕ) (a1 : ℕ) (a2 : ℕ) (a3 : ℕ) (a4 : ℕ) a1.isLt
    a2.isLt a3.isLt a4.isLt (ggTP_finK_true a0) hv
  rw [ggTP_findC_eq, ggTP_good_eq]
  exact of_decide_eq_true h

private theorem ggTP_cjN_lt_fin : ∀ a : Fin 36, ∀ b : Fin 36, cjN a b < 36 := by
  decide +kernel

private theorem ggTP_cjN_lt {a b : ℕ} (ha : a < 36) (hb : b < 36) : cjN a b < 36 :=
  ggTP_cjN_lt_fin ⟨a, ha⟩ ⟨b, hb⟩

private theorem ggTP_rl_mul_self_fin : ∀ i : Fin 36, rl i * rl i = 1 := by
  decide +kernel

private theorem ggTP_rl_mul_self {i : ℕ} (hi : i < 36) : rl i * rl i = 1 :=
  ggTP_rl_mul_self_fin ⟨i, hi⟩

private theorem ggTP_r_lt_fin : ∀ c : Fin 36, ggTP_r c < 36 := by
  decide +kernel

private theorem ggTP_r_lt {c : ℕ} (hc : c < 36) : ggTP_r c < 36 :=
  ggTP_r_lt_fin ⟨c, hc⟩

private theorem ggTP_mem_fix1_fin : ∀ c : Fin 36, ∀ i : Fin 36,
    ((i : ℕ) ∈ fix1 (c : ℕ) ↔ i ≠ c ∧ cjN (i : ℕ) (c : ℕ) = (c : ℕ)) := by
  decide +kernel

private theorem ggTP_mem_fix1 {c i : ℕ} (hc : c < 36) (hi : i < 36) :
    (i ∈ fix1 c ↔ i ≠ c ∧ cjN i c = c) := by
  simpa using ggTP_mem_fix1_fin ⟨c, hc⟩ ⟨i, hi⟩

private theorem ggTP_mem_fix1_lt {c i : ℕ} (h : i ∈ fix1 c) : i < 36 := by
  simp only [fix1, zset, Finset.mem_filter] at h
  exact Finset.mem_range.mp h.1

private theorem ggTP_fixMask_testBit_fin : ∀ c : Fin 36, ∀ i : Fin 36,
    (ggTP_fixMaskOf (c : ℕ)).testBit (i : ℕ) = true ↔
      i ≠ c ∧ cjN (i : ℕ) (c : ℕ) = (c : ℕ) := by
  decide +kernel

private theorem ggTP_fixMask_testBit {c i : ℕ} (hc : c < 36) (hi : i < 36) :
    (ggTP_fixMaskOf c).testBit i = true ↔ i ≠ c ∧ cjN i c = c := by
  simpa using ggTP_fixMask_testBit_fin ⟨c, hc⟩ ⟨i, hi⟩

private theorem ggTP_ofMask_fixMask {c : ℕ} (hc : c < 36) :
    ggTP_ofMask (ggTP_fixMaskOf c) = fix1 c := by
  ext i
  rw [ggTP_mem_ofMask]
  constructor
  · rintro ⟨hi, hbit⟩
    exact (ggTP_mem_fix1 hc hi).mpr ((ggTP_fixMask_testBit hc hi).mp hbit)
  · intro h
    have hi : i < 36 := ggTP_mem_fix1_lt h
    exact ⟨hi, (ggTP_fixMask_testBit hc hi).mpr ((ggTP_mem_fix1 hc hi).mp h)⟩

private def ggTP_seedK (c : ℕ) : ℕ := Nat.lor (ggTP_fixK c) (Nat.shiftLeft 1 (ggTP_rK c))

private theorem ggTP_closure_chk : GGTPK.allK 36 (fun c =>
    Nat.beq (Nat.land (GGTPK.stepK (GGTPK.stepK (GGTPK.stepK (ggTP_seedK c)))) 68719476735)
      68719476735) = true := by
  decide +kernel

private theorem ggTP_cjGen_insert_fix1 {c : ℕ} (hc : c < 36) :
    CjGen (insert (ggTP_r c) (fix1 c)) := by
  intro J hJ hJcl hXJ
  have h0 : ∀ i < 36, GGTPK.bitK (ggTP_seedK c) i = true → i ∈ J := by
    intro i hi h
    unfold ggTP_seedK at h
    rw [GGTPK.bitK_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [← ggTP_fix_eq, GGTPK.bitK_eq] at h
      exact hXJ (Finset.mem_insert_of_mem
        ((ggTP_mem_fix1 hc hi).mpr ((ggTP_fixMask_testBit hc hi).mp h)))
    · rw [GGTPK.bitK_shift1 h, ← ggTP_r_eq]
      exact hXJ (Finset.mem_insert_self _ _)
  have h3 := GGTPK.stepK_sub hJcl (GGTPK.stepK_sub hJcl (GGTPK.stepK_sub hJcl h0))
  refine Finset.Subset.antisymm hJ fun i hi => ?_
  have hi' : i < 36 := Finset.mem_range.mp hi
  exact h3 i hi' (GGTPK.bitK_of_full
    (Nat.eq_of_beq_eq_true (GGTPK.allK_spec ggTP_closure_chk c hc)) hi')

private theorem ggTP_cjN_eq_of_comm {i j : ℕ} (hi : i < 36) (hj : j < 36)
    (h : rl i * rl j = rl j * rl i) : cjN i j = j := by
  have hself : rl i * rl i = 1 := ggTP_rl_mul_self hi
  have h1 : rl i * rl j * rl i = rl j := by
    rw [h, mul_assoc, hself, mul_one]
  have h2 : rl i * rl j * rl i = rl (cjN i j) := rl_conj hi hj
  have h3 : rl (cjN i j) = rl j := by rw [← h2, h1]
  exact rl_injOn (ggTP_cjN_lt hi hj) hj h3

private theorem ggTP_adj {i j : ℕ} (hi : i < 36) (hj : j < 36)
    (h3 : (rl i * rl j) ^ 3 = 1) (hne : rl i ≠ rl j) :
    i ≠ j ∧ cjN i j ≠ j := by
  constructor
  · intro hij
    exact hne (by rw [hij])
  · intro hc
    have h1 : rl i * rl j * rl i = rl j := by
      have h := rl_conj hi hj
      rw [hc] at h
      exact h
    have h2 : (rl i * rl j) ^ 2 = 1 := by
      rw [pow_two]
      calc (rl i * rl j) * (rl i * rl j)
          = ((rl i * rl j) * rl i) * rl j := (mul_assoc (rl i * rl j) (rl i) (rl j)).symm
        _ = rl j * rl j := by rw [h1]
        _ = 1 := ggTP_rl_mul_self hj
    have hst : rl i * rl j = 1 := by
      have h4 : (rl i * rl j) ^ 3 = (rl i * rl j) ^ 2 * (rl i * rl j) := by rw [pow_succ]
      rw [h4, h2, one_mul] at h3
      exact h3
    have heq : rl i = rl j := by
      calc rl i = rl i * 1 := by rw [mul_one]
        _ = rl i * (rl j * rl j) := by rw [ggTP_rl_mul_self hj]
        _ = (rl i * rl j) * rl j := by rw [mul_assoc]
        _ = 1 * rl j := by rw [hst]
        _ = rl j := by rw [one_mul]
    exact hne heq

private theorem ggTP_idx_refl36 : idx refl36 = Finset.range 36 := by
  ext i
  simp only [idx, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.1, fun h => ⟨h, rl_mem h⟩⟩

private theorem ggTP_idx_image {g : Fin 5 → Mat6} {a : Fin 5 → ℕ}
    (ha_lt : ∀ i, a i < 36) (ha : ∀ i, rl (a i) = g i) :
    idx (Finset.univ.image g) = Finset.univ.image a := by
  ext i
  simp only [idx, Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hi, j, hgj⟩
    exact ⟨j, rl_injOn (ha_lt j) hi (by rw [ha j, hgj])⟩
  · rintro ⟨j, rfl⟩
    exact ⟨ha_lt j, j, (ha j).symm⟩

private theorem ggTP_conjGenerates_of_cjGen {X : Finset Mat6} (hX : X ⊆ refl36)
    (h : CjGen (idx X)) : ConjGenerates refl36 X := by
  intro S hS hScl hXS
  have hSidx : idx S ⊆ Finset.range 36 := fun i hi => (Finset.mem_filter.mp hi).1
  have hcl : CjClosed (idx S) := conjClosed_idx hS hScl
  have hsub : idx X ⊆ idx S := idx_mono hXS
  have hfull : idx S = Finset.range 36 := h (idx S) hSidx hcl hsub
  have hidx : idx S = idx refl36 := by rw [hfull, ggTP_idx_refl36]
  exact idx_injOn hS (Finset.Subset.refl refl36) hidx

theorem ggTPA5Chain_completes (g : Fin 5 → E6Dep.Mat6) (hg : ∀ i, g i ∈ E6Dep.refl36)
    (hcomm : ∀ i j : Fin 5, i.val + 2 ≤ j.val → g i * g j = g j * g i)
    (hbraid : ∀ i j : Fin 5, j.val = i.val + 1 → (g i * g j) ^ 3 = 1 ∧ g i ≠ g j) :
    ∃ r ∈ E6Dep.refl36, E6Dep.ConjGenerates E6Dep.refl36 (insert r (Finset.univ.image g)) := by
  classical
  choose a ha using fun i => exists_rl_of_mem (hg i)
  have ha_lt : ∀ i, a i < 36 := fun i => (ha i).1
  have ha_eq : ∀ i, rl (a i) = g i := fun i => (ha i).2
  have comm : ∀ i j : Fin 5, i.val + 2 ≤ j.val → cjN (a i) (a j) = a j := by
    intro i j hij
    apply ggTP_cjN_eq_of_comm (ha_lt i) (ha_lt j)
    have h := hcomm i j hij
    rw [← ha_eq i, ← ha_eq j] at h
    exact h
  have adj : ∀ i j : Fin 5, j.val = i.val + 1 → a i ≠ a j ∧ cjN (a i) (a j) ≠ a j := by
    intro i j hij
    obtain ⟨h3, hne⟩ := hbraid i j hij
    have h3' : (rl (a i) * rl (a j)) ^ 3 = 1 := by
      rw [ha_eq i, ha_eq j]
      exact h3
    have hne' : rl (a i) ≠ rl (a j) := by
      rw [ha_eq i, ha_eq j]
      exact hne
    exact ggTP_adj (ha_lt i) (ha_lt j) h3' hne'
  have hvalid : ggTP_valid (a 0) (a 1) (a 2) (a 3) (a 4) := by
    have h01 := adj 0 1 (by decide)
    have h12 := adj 1 2 (by decide)
    have h23 := adj 2 3 (by decide)
    have h34 := adj 3 4 (by decide)
    have c02 := comm 0 2 (by decide)
    have c03 := comm 0 3 (by decide)
    have c04 := comm 0 4 (by decide)
    have c13 := comm 1 3 (by decide)
    have c14 := comm 1 4 (by decide)
    have c24 := comm 2 4 (by decide)
    simp only [ggTP_valid, ggTP_pre4, ggTP_pre3, ggTP_pre2, ggTP_pre1]
    exact ⟨⟨⟨⟨h01.1, h01.2⟩, h12.1, h12.2, c02⟩, h23.1, h23.2, c03, c13⟩, h34.1, h34.2,
      c04, c14, c24⟩
  let c : ℕ := ggTP_findC (a 0) (a 1) (a 2) (a 3) (a 4)
  have hfin : ggTP_good (a 0) (a 1) (a 2) (a 3) (a 4) c :=
    ggTP_finite ⟨a 0, ha_lt 0⟩ ⟨a 1, ha_lt 1⟩ ⟨a 2, ha_lt 2⟩ ⟨a 3, ha_lt 3⟩
      ⟨a 4, ha_lt 4⟩ hvalid
  obtain ⟨hc_lt, h0, h1, h2, h3, h4, hr_ne, hr_comm, hmask⟩ := hfin
  have hc_comm : ∀ i : Fin 5, a i ≠ c ∧ cjN (a i) c = c := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hS : {a 0, a 1, a 2, a 3, a 4} = Finset.univ.image a := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  have hfixinv : fix1 c ⊆ ggTP_intervals (a 0) (a 1) (a 2) (a 3) (a 4) := by
    rw [← ggTP_ofMask_fixMask hc_lt]
    exact Finset.Subset.trans (ggTP_ofMask_subset_of_and hmask)
      (ggTP_ofMask_intervalsMask_subset (a 0) (a 1) (a 2) (a 3) (a 4))
  have hgenFix : CjGen (insert (ggTP_r c) (fix1 c)) := ggTP_cjGen_insert_fix1 hc_lt
  have hgen : CjGen (insert (ggTP_r c) (Finset.univ.image a)) := by
    intro J hJsub hJcl hXJ
    have hchainJ : ∀ i : Fin 5, a i ∈ J := by
      intro i
      exact hXJ (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
    have hintervals : ggTP_intervals (a 0) (a 1) (a 2) (a 3) (a 4) ⊆ J :=
      ggTP_intervals_subset hJcl (hchainJ 0) (hchainJ 1) (hchainJ 2) (hchainJ 3) (hchainJ 4)
    have hfixJ : fix1 c ⊆ J := Finset.Subset.trans hfixinv hintervals
    have hYsub : insert (ggTP_r c) (fix1 c) ⊆ J := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hXJ (Finset.mem_insert_self _ _)
      · exact hfixJ hx
    exact hgenFix J hJsub hJcl hYsub
  have hYsub' : insert (rl (ggTP_r c)) (Finset.univ.image g) ⊆ refl36 := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact rl_mem (ggTP_r_lt hc_lt)
    · rw [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact hg i
  have hidxY : idx (insert (rl (ggTP_r c)) (Finset.univ.image g)) =
      insert (ggTP_r c) (Finset.univ.image a) := by
    obtain ⟨r', hr'lt, hr'l, hidx⟩ := idx_insert (rl_mem (ggTP_r_lt hc_lt)) (Finset.univ.image g)
    have hr'eq : r' = ggTP_r c := rl_injOn hr'lt (ggTP_r_lt hc_lt) hr'l
    rw [hidx, hr'eq, ggTP_idx_image ha_lt ha_eq]
  refine ⟨rl (ggTP_r c), rl_mem (ggTP_r_lt hc_lt), ?_⟩
  exact ggTP_conjGenerates_of_cjGen hYsub' (by rw [hidxY]; exact hgen)

end CFSG.StandardType

end
