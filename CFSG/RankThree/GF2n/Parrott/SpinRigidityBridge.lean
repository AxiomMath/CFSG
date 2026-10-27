module

public import CFSG.RankThree.GF2n.Parrott.SpinRigidityChecks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import Certificates.Data.ParrottSpin
public import Certificates.Data.ParrottPSp43

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def evalSpinWord {n : ℕ} {M : Type*} [Monoid M] (g : Fin n → M)
    (w : List (Fin n × ℕ)) : M :=
  (w.map fun l => g l.1 ^ l.2).prod

theorem evalSpinWord_nil {n : ℕ} {M : Type*} [Monoid M] (g : Fin n → M) :
    evalSpinWord g [] = 1 := rfl

theorem evalSpinWord_cons {n : ℕ} {M : Type*} [Monoid M] (g : Fin n → M) (l : Fin n × ℕ)
    (w : List (Fin n × ℕ)) : evalSpinWord g (l :: w) = g l.1 ^ l.2 * evalSpinWord g w := by
  simp [evalSpinWord]

theorem map_evalSpinWord {n : ℕ} {M N : Type*} [Monoid M] [Monoid N] (φ : M →* N)
    (g : Fin n → M) (w : List (Fin n × ℕ)) :
    φ (evalSpinWord g w) = evalSpinWord (fun i => φ (g i)) w := by
  induction w with
  | nil => simp [evalSpinWord_nil]
  | cons l w ih => rw [evalSpinWord_cons, evalSpinWord_cons, map_mul, map_pow, ih]

theorem evalSpinWord_congr {n : ℕ} {M N : Type*} [Monoid M] [Monoid N] (φ ψ : M →* N)
    (g : Fin n → M) (h : ∀ i, φ (g i) = ψ (g i)) (w : List (Fin n × ℕ)) :
    φ (evalSpinWord g w) = ψ (evalSpinWord g w) := by
  rw [map_evalSpinWord, map_evalSpinWord]
  simp only [h]

theorem evalSpinWord_congr_mem {n : ℕ} {M : Type*} [Monoid M] (g g' : Fin n → M)
    (w : List (Fin n × ℕ)) (h : ∀ l ∈ w, g l.1 = g' l.1) :
    evalSpinWord g w = evalSpinWord g' w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [evalSpinWord_cons, evalSpinWord_cons, h l List.mem_cons_self,
      ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]

theorem commute_evalSpinWord {n : ℕ} {M : Type*} [Monoid M] (X : M) (g : Fin n → M)
    (w : List (Fin n × ℕ)) (h : ∀ l ∈ w, Commute X (g l.1)) : Commute X (evalSpinWord g w) := by
  induction w with
  | nil => rw [evalSpinWord_nil]; exact Commute.one_right X
  | cons l w ih =>
    rw [evalSpinWord_cons]
    exact Commute.mul_right (Commute.pow_right (h l List.mem_cons_self) _)
      (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

theorem spin_x45_mem : x45 ∈ QA45.originalSubgroup := by
  rw [QA45_closure]
  exact Subgroup.subset_closure (by simp)

theorem spin_y45_mem : y45 ∈ QA45.originalSubgroup := by
  rw [QA45_closure]
  exact Subgroup.subset_closure (by simp)

theorem spin_f45_mem : f45 ∈ QA45.originalSubgroup := by
  rw [QA45_closure]
  exact Subgroup.subset_closure (by simp)

@[expose] def spinGenA : Fin 3 → A45
  | 0 => ⟨x45, spin_x45_mem⟩
  | 1 => ⟨y45, spin_y45_mem⟩
  | 2 => ⟨f45, spin_f45_mem⟩

@[expose] def spinE27a : A45 :=
  evalSpinWord spinGenA [(1, 1), (0, 1), (1, 1), (2, 1), (1, 2), (2, 1), (1, 1), (0, 1), (1, 1),
    (0, 1), (1, 2)]

@[expose] def spinE27b : A45 :=
  evalSpinWord spinGenA [(2, 1), (1, 4), (2, 1), (1, 3), (2, 1), (1, 2), (2, 1), (1, 1), (0, 1)]

@[expose] def spinE27c : A45 := evalSpinWord spinGenA [(1, 4), (0, 1), (1, 1), (0, 1)]

@[expose] def spinE27 : Subgroup A45 := Subgroup.closure {spinE27a, spinE27b, spinE27c}

namespace SpinRigid

@[expose] def permTab (p : P45) : List ℕ := (List.finRange 45).map fun i => (p i).val

theorem getD_permTab (p : P45) (j : Fin 45) : (permTab p).getD j 0 = (p j).val := by
  have hj : (j : ℕ) < (permTab p).length := by simp [permTab]
  rw [List.getD_eq_getElem _ _ hj]
  simp [permTab]

theorem permTab_mul (p q : P45) : permTab (p * q) = tcomp (permTab p) (permTab q) := by
  unfold tcomp
  have hq : permTab q = (List.finRange 45).map fun i => (q i).val := rfl
  rw [hq, List.map_map]
  conv_lhs => unfold permTab
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Equiv.Perm.mul_apply]
  exact (getD_permTab p (q i)).symm

theorem permTab_one : permTab (1 : P45) = tone := by
  unfold permTab tone
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem permTab_pow (p : P45) (n : ℕ) : permTab (p ^ n) = tpow (permTab p) n := by
  induction n with
  | zero => simp [tpow, permTab_one]
  | succ n ih => rw [pow_succ, permTab_mul, ih, tpow]

theorem permTab_injective : Function.Injective permTab := by
  intro p q h
  ext j
  have h1 := getD_permTab p j
  have h2 := getD_permTab q j
  rw [h] at h1
  have := h1.symm.trans h2
  exact this

@[expose] def spinN2 : A45 := evalSpinWord spinGenA [(1, 1), (2, 1), (1, 4), (0, 1), (1, 4)]

@[expose] def spinG5 : Fin 5 → A45
  | 0 => spinGenA 0
  | 1 => spinN2
  | 2 => spinE27a
  | 3 => spinE27b
  | 4 => spinE27c

theorem spinG5_eq (i : Fin 5) : spinG5 i = evalSpinWord spinGenA (g5words i) := by
  fin_cases i <;> rfl

theorem permTab_coe_mul (a b : A45) :
    permTab ((a * b : A45) : P45) = tcomp (permTab a) (permTab b) := by
  rw [Subgroup.coe_mul, permTab_mul]

theorem permTab_coe_one : permTab (((1 : A45)) : P45) = tone := by
  rw [Subgroup.coe_one, permTab_one]

theorem permTab_coe_pow (a : A45) (n : ℕ) :
    permTab ((a ^ n : A45) : P45) = tpow (permTab a) n := by
  rw [Subgroup.coe_pow, permTab_pow]

theorem permTab_coe_evalSpinWord {n : ℕ} (g : Fin n → A45) (w : List (Fin n × ℕ)) :
    permTab ((evalSpinWord g w : A45) : P45) = evalT (fun i => permTab (g i : P45)) w := by
  induction w with
  | nil => rw [evalSpinWord_nil, permTab_coe_one]; rfl
  | cons l w ih => rw [evalSpinWord_cons, permTab_coe_mul, permTab_coe_pow, ih, evalT]

theorem eq_of_permTab_eq {a b : A45} (h : permTab (a : P45) = permTab (b : P45)) : a = b :=
  Subtype.ext (permTab_injective h)

theorem permTab_x45 : permTab x45 = tx := by decide +kernel

theorem permTab_y45 : permTab y45 = ty := by decide +kernel

theorem permTab_f45 : permTab f45 = tf := by decide +kernel

theorem permTab_spinGenA (i : Fin 3) : permTab ((spinGenA i : A45) : P45) = t3 i := by
  fin_cases i
  · exact permTab_x45
  · exact permTab_y45
  · exact permTab_f45

theorem permTab_spinG5 (i : Fin 5) : permTab ((spinG5 i : A45) : P45) = t5 i := by
  have h : (fun j => permTab ((spinGenA j : A45) : P45)) = t3 := funext permTab_spinGenA
  rw [spinG5_eq, permTab_coe_evalSpinWord, h]
  fin_cases i <;> rfl

theorem spin_x_sq : spinGenA 0 * spinGenA 0 = 1 := by
  apply eq_of_permTab_eq
  rw [permTab_coe_mul, permTab_coe_one, permTab_spinGenA]
  exact tab_x_sq

theorem spinG5_norm (p : Fin 5 × Fin 5 × (ℕ × ℕ × ℕ)) (hp : p ∈ normData) :
    spinG5 p.1 * spinG5 p.2.1 = evalSpinWord spinG5 (mWord p.2.2) * spinG5 p.1 := by
  apply eq_of_permTab_eq
  rw [permTab_coe_mul, permTab_coe_mul, permTab_coe_evalSpinWord]
  simp only [permTab_spinG5]
  exact tab_norm p hp

theorem spinG5_rN : evalSpinWord spinG5 rN = 1 := by
  apply eq_of_permTab_eq
  rw [permTab_coe_evalSpinWord, permTab_coe_one]
  simp only [permTab_spinG5]
  exact tab_rN

theorem spinG5_st4 (i : Fin 8) :
    spinGenA 1 * evalSpinWord spinG5 (st4 i).1 = evalSpinWord spinG5 (st4 i).2 * spinGenA 1 := by
  apply eq_of_permTab_eq
  rw [permTab_coe_mul, permTab_coe_mul, permTab_coe_evalSpinWord, permTab_coe_evalSpinWord]
  simp only [permTab_spinG5, permTab_spinGenA]
  exact tab_st4 i

theorem spin_xy9 : (spinGenA 0 * spinGenA 1) ^ 9 = 1 := by
  apply eq_of_permTab_eq
  rw [permTab_coe_pow, permTab_coe_mul, permTab_coe_one]
  simp only [permTab_spinGenA]
  exact tab_xy9

theorem spin_f_word :
    spinGenA 2 = spinGenA 1 ^ 4 * spinN2 * spinGenA 1 * spinGenA 0 * spinGenA 1 := by
  apply eq_of_permTab_eq
  have h1 := permTab_spinG5 1
  rw [permTab_coe_mul, permTab_coe_mul, permTab_coe_mul, permTab_coe_mul, permTab_coe_pow]
  simp only [permTab_spinGenA]
  have h2 : permTab ((spinN2 : A45) : P45) = tN2 := h1
  rw [h2]
  exact tab_f

theorem bitmask_lt (v : V) : bitmask v < 256 := by
  unfold bitmask
  rw [Fin.sum_univ_eight]
  have h0 : (v 0).val < 2 := ZMod.val_lt _
  have h1 : (v 1).val < 2 := ZMod.val_lt _
  have h2 : (v 2).val < 2 := ZMod.val_lt _
  have h3 : (v 3).val < 2 := ZMod.val_lt _
  have h4 : (v 4).val < 2 := ZMod.val_lt _
  have h5 : (v 5).val < 2 := ZMod.val_lt _
  have h6 : (v 6).val < 2 := ZMod.val_lt _
  have h7 : (v 7).val < 2 := ZMod.val_lt _
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.shiftLeft_eq]
  norm_num
  omega

theorem bitmask_zero : bitmask (0 : V) = 0 := by
  unfold bitmask
  simp

theorem bitmask_add (v w : V) : bitmask (v + w) = bitmask v ^^^ bitmask w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  by_cases hi : i < 8
  · have h1 := testBit_bitmask (v + w) ⟨i, hi⟩
    have h2 := testBit_bitmask v ⟨i, hi⟩
    have h3 := testBit_bitmask w ⟨i, hi⟩
    simp only [Pi.add_apply] at h1
    simp only at h1 h2 h3
    rw [h1, h2, h3]
    have key : ∀ a b : ZMod 2,
        decide ((a + b).val = 1) = (decide (a.val = 1) ^^ decide (b.val = 1)) := by decide
    exact key _ _
  · have hl : ∀ u : V, (bitmask u).testBit i = false := fun u =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (bitmask_lt u)
        (by calc 256 = 2 ^ 8 := by norm_num
                 _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hl, hl, hl]
    rfl

theorem bapply_zero (A : B8) : bapply A 0 = 0 := by
  simp [bapply]

theorem ite_testBit (b : Bool) (c i : ℕ) :
    (if b = true then c else 0).testBit i = (b && c.testBit i) := by
  cases b <;> simp

theorem bool_xor_merge16 (p0 p1 p2 p3 p4 p5 p6 p7 q0 q1 q2 q3 q4 q5 q6 q7 : Bool) :
    ((((((((p0 ^^ q0) ^^ (p1 ^^ q1)) ^^ (p2 ^^ q2)) ^^ (p3 ^^ q3)) ^^ (p4 ^^ q4)) ^^
      (p5 ^^ q5)) ^^ (p6 ^^ q6)) ^^ (p7 ^^ q7)) =
    ((((((((p0 ^^ p1) ^^ p2) ^^ p3) ^^ p4) ^^ p5) ^^ p6) ^^ p7) ^^
      (((((((q0 ^^ q1) ^^ q2) ^^ q3) ^^ q4) ^^ q5) ^^ q6) ^^ q7)) := by
  revert p0 p1 p2 p3 p4 p5 p6 p7 q0 q1 q2 q3 q4 q5 q6 q7
  decide +kernel

theorem bapply_xor (A : B8) (m m' : ℕ) :
    bapply A (m ^^^ m') = bapply A m ^^^ bapply A m' := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [bapply, Nat.testBit_xor, ite_testBit, Bool.and_xor_distrib_right]
  exact bool_xor_merge16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem bapply_bit0 (A : B8) : bapply A 1 = A.c0 := by
  simp (config := {decide := true}) [bapply]

theorem bapply_bit1 (A : B8) : bapply A 2 = A.c1 := by
  simp (config := {decide := true}) [bapply]

theorem bapply_bit2 (A : B8) : bapply A 4 = A.c2 := by
  simp (config := {decide := true}) [bapply]

theorem bapply_bit3 (A : B8) : bapply A 8 = A.c3 := by
  simp (config := {decide := true}) [bapply]

theorem bapply_bit4 (A : B8) : bapply A 16 = A.c4 := by
  simp (config := {decide := true}) [bapply]

theorem bapply_bit5 (A : B8) : bapply A 32 = A.c5 := by
  simp (config := {decide := true}) [bapply]

theorem bapply_bit6 (A : B8) : bapply A 64 = A.c6 := by
  simp (config := {decide := true}) [bapply]

theorem bapply_bit7 (A : B8) : bapply A 128 = A.c7 := by
  simp (config := {decide := true}) [bapply]

theorem eq_sum_basis (v : V) : v = ∑ j, v j • basis j := by
  ext i
  simp [basis, Finset.sum_apply, Pi.single_apply]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem additive_decomp (f : V → ℕ) (hadd : ∀ u w, f (u + w) = f u ^^^ f w) (h0 : f 0 = 0)
    (v : V) :
    f v = (if v 0 = 1 then f (basis 0) else 0) ^^^ (if v 1 = 1 then f (basis 1) else 0) ^^^
      (if v 2 = 1 then f (basis 2) else 0) ^^^ (if v 3 = 1 then f (basis 3) else 0) ^^^
      (if v 4 = 1 then f (basis 4) else 0) ^^^ (if v 5 = 1 then f (basis 5) else 0) ^^^
      (if v 6 = 1 then f (basis 6) else 0) ^^^ (if v 7 = 1 then f (basis 7) else 0) := by
  have hs : ∀ (c : ZMod 2) (j : Fin 8), f (c • basis j) = if c = 1 then f (basis j) else 0 := by
    intro c j
    rcases zmod2_cases c with rfl | rfl
    · simp [h0]
    · simp
  conv_lhs => rw [eq_sum_basis v, Fin.sum_univ_eight]
  rw [hadd, hadd, hadd, hadd, hadd, hadd, hadd]
  simp only [hs]

@[expose] def colsOf (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) : B8 :=
  ⟨bitmask (A *ᵥ basis 0), bitmask (A *ᵥ basis 1), bitmask (A *ᵥ basis 2),
    bitmask (A *ᵥ basis 3), bitmask (A *ᵥ basis 4), bitmask (A *ᵥ basis 5),
    bitmask (A *ᵥ basis 6), bitmask (A *ᵥ basis 7)⟩

theorem bapply_colsOf (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) (v : V) :
    bapply (colsOf A) (bitmask v) = bitmask (A *ᵥ v) := by
  have hf : ∀ u w : V, bapply (colsOf A) (bitmask (u + w)) =
      bapply (colsOf A) (bitmask u) ^^^ bapply (colsOf A) (bitmask w) := by
    intro u w
    rw [bitmask_add, bapply_xor]
  have hg : ∀ u w : V, bitmask (A *ᵥ (u + w)) = bitmask (A *ᵥ u) ^^^ bitmask (A *ᵥ w) := by
    intro u w
    rw [Matrix.mulVec_add, bitmask_add]
  have hb : ∀ j : Fin 8, bapply (colsOf A) (bitmask (basis j)) = bitmask (A *ᵥ basis j) := by
    intro j
    fin_cases j <;>
      simp [bitmask_basis, bapply_bit0, bapply_bit1, bapply_bit2, bapply_bit3, bapply_bit4,
        bapply_bit5, bapply_bit6, bapply_bit7, colsOf]
  rw [additive_decomp (fun v => bapply (colsOf A) (bitmask v)) hf
      (by simp [bitmask_zero, bapply_zero]) v,
    additive_decomp (fun v => bitmask (A *ᵥ v)) hg (by simp [bitmask_zero]) v]
  simp only [hb]

theorem colsOf_mul (A B : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    colsOf (A * B) = bmul (colsOf A) (colsOf B) := by
  have h : ∀ j : Fin 8, bitmask ((A * B) *ᵥ basis j) =
      bapply (colsOf A) (bitmask (B *ᵥ basis j)) := by
    intro j
    rw [bapply_colsOf, Matrix.mulVec_mulVec]
  apply B8.ext
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h 5
  · exact h 6
  · exact h 7

theorem colsOf_one : colsOf (1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = bone := by
  have h : ∀ j : Fin 8, bitmask ((1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ basis j) =
      1 <<< (j : ℕ) := by
    intro j
    rw [Matrix.one_mulVec, bitmask_basis]
  apply B8.ext
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h 5
  · exact h 6
  · exact h 7

theorem fin8_cases (j : Fin 8) :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by
  revert j
  decide

theorem colsOf_injective : Function.Injective colsOf := by
  intro A B h
  simp only [colsOf, B8.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hj : ∀ j : Fin 8, A *ᵥ basis j = B *ᵥ basis j := by
    intro j
    apply bitmask_injective
    rcases fin8_cases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
  ext i j
  have := congrFun (hj j) i
  simpa [basis, Matrix.mulVec_single_one] using this

theorem colsOf_pow (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) (n : ℕ) :
    colsOf (A ^ n) = bpow (colsOf A) n := by
  induction n with
  | zero => rw [pow_zero, colsOf_one]; rfl
  | succ n ih => rw [pow_succ, colsOf_mul, ih]; rfl

theorem colsOf_evalSpinWord {n : ℕ} (G : Fin n → Matrix (Fin 8) (Fin 8) (ZMod 2))
    (gb : Fin n → B8) (h : ∀ i, colsOf (G i) = gb i) (w : List (Fin n × ℕ)) :
    colsOf (evalSpinWord G w) = evalB gb w := by
  induction w with
  | nil => rw [evalSpinWord_nil, colsOf_one]; rfl
  | cons l w ih => rw [evalSpinWord_cons, colsOf_mul, colsOf_pow, h, ih]; rfl

theorem bnd_iff (A : B8) : bnd A = true ↔
    A.c0 < 256 ∧ A.c1 < 256 ∧ A.c2 < 256 ∧ A.c3 < 256 ∧ A.c4 < 256 ∧ A.c5 < 256 ∧ A.c6 < 256 ∧
      A.c7 < 256 := by
  simp [bnd, and_assoc]

theorem xor_lt_256 {a b : ℕ} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 :=
  Nat.xor_lt_two_pow (n := 8) ha hb

theorem ite_lt_256 (b : Bool) {c : ℕ} (hc : c < 256) : (if b = true then c else 0) < 256 := by
  cases b <;> simp [hc]

theorem bapply_lt (A : B8) (hA : bnd A = true) (m : ℕ) : bapply A m < 256 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := (bnd_iff A).1 hA
  unfold bapply
  exact xor_lt_256 (xor_lt_256 (xor_lt_256 (xor_lt_256 (xor_lt_256 (xor_lt_256
    (xor_lt_256 (ite_lt_256 _ h0) (ite_lt_256 _ h1)) (ite_lt_256 _ h2)) (ite_lt_256 _ h3))
    (ite_lt_256 _ h4)) (ite_lt_256 _ h5)) (ite_lt_256 _ h6)) (ite_lt_256 _ h7)

theorem bnd_bmul (A B : B8) (hA : bnd A = true) : bnd (bmul A B) = true := by
  rw [bnd_iff]
  exact ⟨bapply_lt A hA _, bapply_lt A hA _, bapply_lt A hA _, bapply_lt A hA _,
    bapply_lt A hA _, bapply_lt A hA _, bapply_lt A hA _, bapply_lt A hA _⟩

theorem bnd_bone : bnd bone = true := by decide

theorem bnd_bpow (A : B8) (n : ℕ) : bnd (bpow A n) = true := by
  induction n with
  | zero => exact bnd_bone
  | succ n ih => exact bnd_bmul _ _ ih

theorem bnd_evalB {n : ℕ} (g : Fin n → B8) (w : List (Fin n × ℕ)) : bnd (evalB g w) = true := by
  cases w with
  | nil => exact bnd_bone
  | cons l w => exact bnd_bmul _ _ (bnd_bpow _ _)

theorem bnd_wcols (T : Fin 8 → B8) (hT : ∀ i, bnd (T i) = true) (w : ℕ) :
    bnd (wcols T w) = true := by
  rw [bnd_iff]
  exact ⟨bapply_lt _ (hT 0) _, bapply_lt _ (hT 1) _, bapply_lt _ (hT 2) _, bapply_lt _ (hT 3) _,
    bapply_lt _ (hT 4) _, bapply_lt _ (hT 5) _, bapply_lt _ (hT 6) _, bapply_lt _ (hT 7) _⟩

@[expose] def vecOfNat (n : ℕ) : V := fun i => ((n >>> (i : ℕ)) % 2 : ℕ)

theorem bitmask_vecOfNat (n : ℕ) (hn : n < 256) : bitmask (vecOfNat n) = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · rw [testBit_bitmask (vecOfNat n) ⟨i, hi⟩]
    have h1 : ((vecOfNat n ⟨i, hi⟩).val = 1) ↔ n.testBit i = true := by
      simp only [vecOfNat, ZMod.val_natCast]
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
      simp
    by_cases h2 : n.testBit i = true
    · simp [h1.2 h2, h2]
    · have : ¬ (vecOfNat n ⟨i, hi⟩).val = 1 := fun h => h2 (h1.1 h)
      simp [this, h2]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (bitmask_lt _)
      (by calc 256 = 2 ^ 8 := by norm_num
               _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
      (by calc 256 = 2 ^ 8 := by norm_num
               _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem exists_colsOf (c : B8) (hc : bnd c = true) :
    ∃ A : Matrix (Fin 8) (Fin 8) (ZMod 2), colsOf A = c := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := (bnd_iff c).1 hc
  refine ⟨Matrix.of fun (i j : Fin 8) => (((c.col j >>> (i : ℕ)) % 2 : ℕ) : ZMod 2), ?_⟩
  have h : ∀ j : Fin 8, c.col j < 256 → bitmask
      ((Matrix.of fun (i j : Fin 8) => (((c.col j >>> (i : ℕ)) % 2 : ℕ) : ZMod 2)) *ᵥ basis j) =
      c.col j := by
    intro j hj
    have e : (Matrix.of fun (i j : Fin 8) =>
        (((c.col j >>> (i : ℕ)) % 2 : ℕ) : ZMod 2)) *ᵥ basis j = vecOfNat (c.col j) := by
      ext i
      simp [basis, vecOfNat]
    rw [e]
    exact bitmask_vecOfNat (c.col j) hj
  apply B8.ext
  · exact h 0 h0
  · exact h 1 h1
  · exact h 2 h2
  · exact h 3 h3
  · exact h 4 h4
  · exact h 5 h5
  · exact h 6 h6
  · exact h 7 h7

@[expose] def colMat (T : Fin 8 → Matrix (Fin 8) (Fin 8) (ZMod 2)) (w : V) :
    Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i k => (T k *ᵥ w) i

theorem colsOf_colMat (T : Fin 8 → Matrix (Fin 8) (Fin 8) (ZMod 2)) (w : V) :
    colsOf (colMat T w) = wcols (fun k => colsOf (T k)) (bitmask w) := by
  have h : ∀ j : Fin 8, bitmask (colMat T w *ᵥ basis j) =
      bapply (colsOf (T j)) (bitmask w) := by
    intro j
    rw [bapply_colsOf]
    congr 1
    ext i
    simp [colMat, basis]
  apply B8.ext
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h 5
  · exact h 6
  · exact h 7

theorem colMat_mul_comm (T : Fin 8 → Matrix (Fin 8) (Fin 8) (ZMod 2)) (v : V)
    (X : Matrix (Fin 8) (Fin 8) (ZMod 2)) (hX : ∀ k, X * T k = T k * X) :
    X * colMat T v = colMat T (X *ᵥ v) := by
  ext i k
  have e : X *ᵥ (T k *ᵥ v) = T k *ᵥ (X *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX k]
  have := congrFun e i
  simpa [colMat, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem commutant_param (T : Fin 8 → Matrix (Fin 8) (Fin 8) (ZMod 2)) (tc : Fin 8 → B8)
    (hT : ∀ k, colsOf (T k) = tc k) (v : ℕ) (hv : v < 256) (binv : B8) (hb : bnd binv = true)
    (hB : bmul (wcols tc v) binv = bone) (X : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (hX : ∀ k, X * T k = T k * X) :
    colsOf X = bmul (wcols tc (bitmask (X *ᵥ vecOfNat v))) binv := by
  obtain ⟨Binv, hBinv⟩ := exists_colsOf binv hb
  have hT' : (fun k => colsOf (T k)) = tc := funext hT
  have hB1 : colMat T (vecOfNat v) * Binv = 1 := by
    apply colsOf_injective
    rw [colsOf_mul, colsOf_colMat, bitmask_vecOfNat v hv, hBinv, colsOf_one, hT']
    exact hB
  have h1 : X = colMat T (X *ᵥ vecOfNat v) * Binv := by
    calc X = X * (colMat T (vecOfNat v) * Binv) := by rw [hB1, mul_one]
      _ = (X * colMat T (vecOfNat v)) * Binv := by rw [mul_assoc]
      _ = colMat T (X *ᵥ vecOfNat v) * Binv := by rw [colMat_mul_comm T _ X hX]
  conv_lhs => rw [h1]
  rw [colsOf_mul, colsOf_colMat, hBinv, hT']

theorem image_spinGenA :
    (QA45.originalSubgroup).subtype '' Set.range spinGenA = ({x45, y45, f45} : Set P45) := by
  ext g
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
    fin_cases i <;> simp [spinGenA]
  · intro hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨spinGenA 0, ⟨0, rfl⟩, rfl⟩
    · exact ⟨spinGenA 1, ⟨1, rfl⟩, rfl⟩
    · exact ⟨spinGenA 2, ⟨2, rfl⟩, rfl⟩

theorem closure_spinGenA : Subgroup.closure (Set.range spinGenA) = ⊤ := by
  apply Subgroup.map_injective (f := (QA45.originalSubgroup).subtype)
    (QA45.originalSubgroup).subtype_injective
  rw [MonoidHom.map_closure, image_spinGenA]
  have htop : (⊤ : Subgroup A45).map (QA45.originalSubgroup).subtype = QA45.originalSubgroup := by
    ext x
    constructor
    · rintro ⟨a, -, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  rw [htop]
  exact QA45_closure.symm

theorem hom_ext_spinGenA {M : Type*} [Monoid M] {φ ψ : A45 →* M}
    (h : ∀ i, φ (spinGenA i) = ψ (spinGenA i)) : φ = ψ :=
  MonoidHom.eq_of_eqOn_dense closure_spinGenA (by
    rintro a ⟨i, rfl⟩
    exact h i)

theorem colsOf_Mx : colsOf Mx = b3 0 := by
  apply B8.ext <;> decide +kernel

theorem colsOf_My : colsOf My = b3 1 := by
  apply B8.ext <;> decide +kernel

theorem colsOf_Mf : colsOf Mf = b3 2 := by
  apply B8.ext <;> decide +kernel

theorem evalB_g5words_zero : evalB b3 (g5words 0) = b3 0 := by
  apply B8.ext <;> decide +kernel

theorem normData_j (p : Fin 5 × Fin 5 × (ℕ × ℕ × ℕ)) (hp : p ∈ normData) :
    2 ≤ (p.2.1 : ℕ) := by
  simp only [normData, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mWord_gen (t : ℕ × ℕ × ℕ) (l : Fin 5 × ℕ) (hl : l ∈ mWord t) : 2 ≤ (l.1 : ℕ) := by
  simp only [mWord, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl <;> (dsimp only; decide)

theorem val_comm {u v : GL8} (h : u * v = v * u) :
    (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) * v = v * u := by
  have := congrArg Units.val h
  simpa only [Units.val_mul] using this

theorem exists_unit_of_cube {U : Matrix (Fin 8) (Fin 8) (ZMod 2)} (h : U ^ 3 = 1) :
    ∃ u : GL8, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = U :=
  ⟨⟨U, U * U, by rw [← pow_three]; exact h, by rw [← pow_three']; exact h⟩, rfl⟩

theorem bnd_xc (w : ℕ) : bnd (xc w) = true :=
  bnd_bmul _ _ (bnd_wcols tcM (fun _ => bnd_evalB _ _) w)

theorem comm_of_relations {G : Type*} [Group G] (a r m W : G) (hρ : r * m = W * r)
    (hσ : a * m = W * a) : (a⁻¹ * r) * m = m * (a⁻¹ * r) := by
  have e1 : a⁻¹ * W = m * a⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hσ, mul_assoc, mul_inv_cancel, mul_one]
  calc a⁻¹ * r * m = a⁻¹ * (r * m) := mul_assoc _ _ _
    _ = a⁻¹ * (W * r) := by rw [hρ]
    _ = (a⁻¹ * W) * r := (mul_assoc _ _ _).symm
    _ = (m * a⁻¹) * r := by rw [e1]
    _ = m * (a⁻¹ * r) := mul_assoc _ _ _

@[expose] def conjRep (u : GL8) (ρ : A45 →* GL8) : A45 →* GL8 :=
  (MulAut.conj u⁻¹ : MulAut GL8).toMonoidHom.comp ρ

theorem conjRep_apply (u : GL8) (ρ : A45 →* GL8) (a : A45) :
    conjRep u ρ a = u⁻¹ * ρ a * u := by
  simp [conjRep]

theorem conjRep_eq_of_mul {u : GL8} {ρ : A45 →* GL8} {a : A45} {τ : GL8}
    (h : ρ a * u = u * τ) : conjRep u ρ a = τ := by
  rw [conjRep_apply, mul_assoc, h, inv_mul_cancel_left]

theorem conjRep_eq_of_comm {u : GL8} {ρ : A45 →* GL8} {a : A45} {τ : GL8} (h1 : ρ a = τ)
    (h2 : u * τ = τ * u) : conjRep u ρ a = τ :=
  conjRep_eq_of_mul (by rw [h1]; exact h2.symm)

end SpinRigid

theorem spinE27a_coe : (spinE27a : P45) = sigma1 := by
  apply SpinRigid.permTab_injective
  have h : SpinRigid.permTab ((SpinRigid.spinG5 2 : A45) : P45) = t5 2 :=
    SpinRigid.permTab_spinG5 2
  rw [show (spinE27a : P45) = ((SpinRigid.spinG5 2 : A45) : P45) from rfl, h]
  decide +kernel

theorem spinE27b_coe : (spinE27b : P45) = sigma2 := by
  apply SpinRigid.permTab_injective
  have h : SpinRigid.permTab ((SpinRigid.spinG5 3 : A45) : P45) = t5 3 :=
    SpinRigid.permTab_spinG5 3
  rw [show (spinE27b : P45) = ((SpinRigid.spinG5 3 : A45) : P45) from rfl, h]
  decide +kernel

end CFSG.RankThree.GF2n.Parrott
