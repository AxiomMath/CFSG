module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQAlg
public import Certificates.Data.Kernel.BabyMonster.CTIB.CosetQ

public section

namespace CertificateChecks.KernelBM.CTIB.CosetQ

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.Monster.B.CTIB.Native CertificateChecks.KernelBM.CTIB

set_option exponentiation.threshold 1024

@[expose] def SymG (G : Array ℕ) : Prop :=
  ∀ i < 22, ∀ j < 22, (G.getD i 0).testBit j = (G.getD j 0).testBit i

theorem fld32_bit (S s : ℕ) {i : ℕ} (hi : i < 32) : (fld32 S s).testBit i = S.testBit (32 * s + i) := by
  rw [fld32_eq, Nat.testBit_and, Nat.testBit_shiftRight, testBit_two_pow_sub_one',
    decide_eq_true hi, Bool.and_true]

theorem land_M22_lt (a : ℕ) : Nat.land a 4194303 < 2 ^ 22 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

theorem land_M22_bit (a : ℕ) {i : ℕ} (hi : i < 22) : (Nat.land a 4194303).testBit i = a.testBit i := by
  rw [land_eq, Nat.testBit_and, M22_eq, testBit_two_pow_sub_one', decide_eq_true hi, Bool.and_true]

theorem xorFields_bit22 (S : ℕ) {v : ℕ} (hv : v < 2 ^ 22) {i : ℕ} (hi : i < 32) :
    (xorFields S v).testBit i = bx (fun m => v.testBit m && (fld32 S m).testBit i) 22 := by
  have h32 : (32 : ℕ) = 22 + 10 := rfl
  rw [xorFields_bit _ hv hi, h32, bx_add, bx_false (n := 10) fun m _ => by
    rw [decide_eq_false (by omega : ¬ 22 + m < 22), Bool.false_and, Bool.false_and], Bool.xor_false]
  refine bx_congr fun m hm => ?_
  rw [fld32_bit _ _ hi, decide_eq_true hm, Bool.true_and, Nat.add_comm i]

theorem betaK_bit (G : Array ℕ) (hG : SymG G) (a b : ℕ) :
    (betaK (loOf G) a b).testBit 0 = corr G a b := sign_eq G hG a b

theorem betaK_lt (LO a b : ℕ) : betaK LO a b < 2 := par32_lt _

@[expose] noncomputable def rowC (LO S i : ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc' => Nat.lor acc' (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.shiftLeft (betaK LO (fld32 S i) (fld32 S j)) j) (Nat.blt i j))) m

theorem rowC_bit (LO S i : ℕ) : ∀ m t, (rowC LO S i m).testBit t =
    (decide (t < m) && decide (i < t) && (betaK LO (fld32 S i) (fld32 S t)).testBit 0)
  | 0, t => by simp [rowC]
  | m + 1, t => by
    have e : rowC LO S i (m + 1) = rowC LO S i m ||| (if i < m then
        betaK LO (fld32 S i) (fld32 S m) <<< m else 0) := by
      change Nat.lor (rowC LO S i m) (Bool.rec (motive := fun _ => Nat) 0
        (Nat.shiftLeft (betaK LO (fld32 S i) (fld32 S m)) m) (Nat.blt i m)) = _
      by_cases h : i < m
      · have hb : Nat.blt i m = true := by rw [Nat.blt_eq]; exact h
        rw [ite_eq_left h, hb]
        rfl
      · have hb : Nat.blt i m = false := Bool.eq_false_iff.2 fun h' => h (by rwa [Nat.blt_eq] at h')
        rw [ite_eq_right h, hb]
        rfl
    rw [e, Nat.testBit_or, rowC_bit LO S i m t]
    have hb := betaK_lt LO (fld32 S i) (fld32 S m)
    rcases Nat.lt_trichotomy t m with h | rfl | h
    · have h1 : t < m + 1 := by omega
      split_ifs
      · rw [Nat.testBit_shiftLeft, decide_eq_false (by omega : ¬ t ≥ m)]
        simp [h, h1]
      · simp [h, h1]
    · split_ifs with hi
      · rw [Nat.testBit_shiftLeft, Nat.sub_self]
        simp [hi]
      · simp [hi]
    · have h1 : ¬ t < m + 1 := by omega
      have h2 : ¬ t < m := by omega
      split_ifs
      · have hb1 : betaK LO (fld32 S i) (fld32 S m) < 2 ^ 1 := hb
        rw [Nat.testBit_shiftLeft, Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hb1 (Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 1 ≤ t - m)))]
        simp [h1, h2]
      · simp [h1, h2]

theorem rowC_lt (LO S i : ℕ) : rowC LO S i 22 < 2 ^ 32 := by
  apply Nat.lt_pow_two_of_testBit
  intro t ht
  rw [rowC_bit, decide_eq_false (by omega : ¬ t < 22)]
  rfl

@[expose] noncomputable def ctabR (LO S : ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (rowC LO S i 22) (Nat.mul (nat_lit 32) i))) m

theorem ctabK_eq (LO S : ℕ) : ctabK LO S = ctabR LO S 22 := rfl

theorem ctabR_eq (LO S : ℕ) : ∀ m, ctabR LO S m = wsum (fun i => rowC LO S i 22) 32 m
  | 0 => rfl
  | m + 1 => by
    have e : ctabR LO S (m + 1) = ctabR LO S m ||| (rowC LO S m 22 <<< (32 * m)) := rfl
    rw [e, ctabR_eq LO S m, or_shiftLeft_eq (wsum_lt (fun i => rowC_lt LO S i) m)]
    rfl

theorem ctabK_bit (LO S : ℕ) {m j : ℕ} (hm : m < 22) (hj : j < 32) :
    (ctabK LO S).testBit (j + 32 * m) =
      (decide (j < 22) && decide (m < j) && (betaK LO (fld32 S m) (fld32 S j)).testBit 0) := by
  rw [ctabK_eq, ctabR_eq, Nat.add_comm, testBit_wsum (fun i => rowC_lt LO S i) hj,
    decide_eq_true hm, Bool.true_and, rowC_bit]

theorem imgF_def (S C a : ℕ) : imgF S C a =
    ((xorFields S (Nat.land a 4194303)) &&& (2 ^ 22 - 1)) |||
      ((((a >>> 22) ^^^ (xorFields S (Nat.land a 4194303) >>> 22)) ^^^
        par32 (Nat.land (xorFields C (Nat.land a 4194303)) (Nat.land a 4194303))) &&& (2 ^ 1 - 1))
        <<< 22 := rfl

theorem imgF_lt (S C a : ℕ) : imgF S C a < 2 ^ 23 := by
  rw [imgF_def]
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_and,
    testBit_two_pow_sub_one', testBit_two_pow_sub_one', decide_eq_false (by omega : ¬ i < 22),
    decide_eq_false (by omega : ¬ i - 22 < 1)]
  simp

theorem par_ctabK (G : Array ℕ) (hG : SymG G) (S a : ℕ) :
    (par32 (Nat.land (xorFields (ctabK (loOf G) S) (Nat.land a 4194303)) (Nat.land a 4194303))).testBit
      0 = quadA G (arrOf S) a := by
  have hq := land_M22_lt a
  have h32 : (32 : ℕ) = 22 + 10 := rfl
  rw [par32_bit, h32, bx_add, bx_false (n := 10) fun j _ => by
      rw [land_eq, Nat.testBit_and, Nat.testBit_lt_two_pow (lt_of_lt_of_le hq
        (Nat.pow_le_pow_right (by decide) (by omega))), Bool.and_false], Bool.xor_false]
  unfold quadA dsum
  refine bx_congr fun j hj => ?_
  rw [land_eq, Nat.testBit_and, xorFields_bit22 _ hq (by omega), bx_and]
  refine bx_congr fun m hm => ?_
  simp only [cc]
  rw [fld32_bit _ _ (by omega), Nat.add_comm, ctabK_bit _ _ hm (by omega), betaK_bit G hG,
    land_M22_bit a hm, land_M22_bit a hj, decide_eq_true hj, Bool.true_and, arrOf_getD S hm,
    arrOf_getD S hj]
  cases a.testBit j <;> cases a.testBit m <;> cases decide (m < j) <;>
    cases corr G (fld32 S m) (fld32 S j) <;> rfl

theorem imgF_ctabK (G : Array ℕ) (hG : SymG G) (S a : ℕ) :
    imgF S (ctabK (loOf G) S) a = autQ (loOf G) S a := by
  rw [autQ_loOf G hG]
  have hq := land_M22_lt a
  refine code_ext (imgF_lt _ _ _) (autApply_lt _ _ _) (fun i hi => ?_) ?_
  · rw [imgF_def, Nat.testBit_or, Nat.testBit_and, testBit_two_pow_sub_one', decide_eq_true hi,
      Bool.and_true, Nat.testBit_shiftLeft, decide_eq_false (by omega : ¬ i ≥ 22), Bool.false_and,
      Bool.or_false, xorFields_bit22 S hq (by omega), autApply_bit G _ _ hi]
    exact bx_congr fun m hm => by rw [land_M22_bit a hm, arrOf_getD S hm]
  · rw [imgF_def, Nat.testBit_or, Nat.testBit_and, testBit_two_pow_sub_one',
      decide_eq_false (Nat.lt_irrefl 22), Bool.and_false, Bool.false_or, Nat.testBit_shiftLeft,
      decide_eq_true (Nat.le_refl 22), Bool.true_and, Nat.sub_self, Nat.testBit_and,
      testBit_two_pow_sub_one', decide_eq_true (by decide : 0 < 1), Bool.and_true, Nat.testBit_xor,
      Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.add_zero, par_ctabK G hG,
      xorFields_bit22 S hq (by omega), autApply_bit22]
    congr 2
    exact bx_congr fun m hm => by rw [land_M22_bit a hm, arrOf_getD S hm]

theorem compAutF_ctabK (G : Array ℕ) (hG : SymG G) (S A : ℕ) :
    compAutF S (ctabK (loOf G) S) A = compAut (loOf G) A S := by
  have h : imgF S (ctabK (loOf G) S) = autQ (loOf G) S := funext (imgF_ctabK G hG S)
  unfold compAutF compAut
  rw [h]

theorem wordKF_eq (G : Array ℕ) (hG : SymG G) (S CT : List ℕ) : ∀ (st : List ℕ) (acc : ℕ),
    (∀ s ∈ st, nthN CT s = ctabK (loOf G) (nthN S s)) →
      wordKF S CT st acc = st.foldl (fun A s => compAut (loOf G) A (nthN S s)) acc
  | [], _, _ => rfl
  | s :: st, acc, h => by
    have e : wordKF S CT (s :: st) acc =
        forceB (compAutF (nthN S s) (nthN CT s) acc) (fun a' => wordKF S CT st a') := rfl
    rw [e, forceB_eq, h s List.mem_cons_self, compAutF_ctabK G hG,
      wordKF_eq G hG S CT st _ fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]
    rfl

end CertificateChecks.KernelBM.CTIB.CosetQ

end
