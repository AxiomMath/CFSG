module

public import Certificates.Data.CFSGNative.G24DC.Check
public import Certificates.Data.G24IdentModel

public section

namespace CFSG.Quasithin.St84.G24DC.Code

open scoped BigOperators
open CFSG.Fischer
open CFSG.LieType.Multipliers.G24 (getD_finRange_map toMat mulArr)
open CFSG.Quasithin.St84.G24DC.Native

@[expose] def decCode (c : Nat) : F4 := ⟨c % 4, Nat.mod_lt _ (by decide)⟩

theorem decCode_eq_of_lt {c : Nat} (h : c < 4) : decCode c = ⟨c, h⟩ := by
  simp [decCode, Nat.mod_eq_of_lt h]

theorem decCode_inj {a b : Nat} (ha : a < 4) (hb : b < 4) (h : decCode a = decCode b) :
    a = b := by
  have h' := congrArg F4.code h
  rw [decCode_eq_of_lt ha, decCode_eq_of_lt hb] at h'
  exact congrArg Fin.val h'

theorem xor_lt {a b : Nat} (ha : a < 4) (hb : b < 4) : a ^^^ b < 4 := by
  interval_cases a <;> interval_cases b <;> decide

theorem decCode_xor {a b : Nat} (ha : a < 4) (hb : b < 4) :
    decCode (a ^^^ b) = decCode a + decCode b := by
  interval_cases a <;> interval_cases b <;> rfl

theorem decCode_scalarMul {a b : Nat} (ha : a < 4) (hb : b < 4) :
    decCode (scalarMul a b) = decCode a * decCode b := by
  interval_cases a <;> interval_cases b <;> rfl

theorem rowVal_lt (r : Row) (j : Nat) : rowVal r j < 4 := by
  unfold rowVal
  have h1 : (r.1.testBit j).toNat ≤ 1 := by cases r.1.testBit j <;> simp
  have h2 : (r.2.testBit j).toNat ≤ 1 := by cases r.2.testBit j <;> simp
  omega

theorem bits_of_rowVal_eq {r s : Row} {j : Nat} (h : rowVal r j = rowVal s j) :
    r.1.testBit j = s.1.testBit j ∧ r.2.testBit j = s.2.testBit j := by
  unfold rowVal at h
  revert h
  cases r.1.testBit j <;> cases r.2.testBit j <;>
    cases s.1.testBit j <;> cases s.2.testBit j <;> simp

theorem mask14_testBit {j : Nat} (hj : j < 14) : mask14.testBit j = true := by
  have hm : mask14 = 2 ^ 14 - 1 := by norm_num [mask14]
  rw [hm, Nat.testBit_two_pow_sub_one]
  simp [hj]

theorem rowVal_canon {r : Row} {j : Nat} (hj : j < 14) :
    rowVal (canon r) j = rowVal r j := by
  unfold canon rowVal
  rw [Nat.testBit_and, Nat.testBit_and, mask14_testBit hj, Bool.and_true, Bool.and_true]

theorem rowVal_omega {u v : Nat} {j : Nat} (hj : j < 14) :
    rowVal (canon (v, u ^^^ v)) j = omegaCode (rowVal (u, v) j) := by
  rw [rowVal_canon hj]
  unfold rowVal omegaCode
  rw [Nat.testBit_xor]
  cases u.testBit j <;> cases v.testBit j <;> rfl

theorem rowVal_omega2 {u v : Nat} {j : Nat} (hj : j < 14) :
    rowVal (canon (u ^^^ v, u)) j = omegaCode (rowVal (u, v) j) ^^^ rowVal (u, v) j := by
  rw [rowVal_canon hj]
  unfold rowVal omegaCode
  rw [Nat.testBit_xor]
  cases u.testBit j <;> cases v.testBit j <;> rfl

theorem rowVal_scale {a u v : Nat} {j : Nat} (hj : j < 14) :
    rowVal (scale a u v) j = scalarMul a (rowVal (u, v) j) := by
  by_cases h0 : a = 0
  · subst a
    have hz : rowVal zeroRow j = 0 := by unfold rowVal zeroRow; simp
    rw [show scale 0 u v = zeroRow from rfl, show scalarMul 0 (rowVal (u, v) j) = 0 from rfl, hz]
  · by_cases h1 : a = 1
    · subst a
      simp [scale, scalarMul, rowVal_canon hj]
    · by_cases h2 : a = 2
      · subst a
        simp [scale, scalarMul, rowVal_omega hj]
      · simp [scale, scalarMul, h0, h1, h2, rowVal_omega2 hj]

def BoundedMat (A : Mat) : Prop :=
  ∀ i, (A.getD i zeroRow).1 < 2 ^ 14 ∧ (A.getD i zeroRow).2 < 2 ^ 14

@[expose] def decRow (r : Row) : Array F4 :=
  ((List.finRange 14).map fun j => decCode (rowVal r j.val)).toArray

@[expose] def decMat (A : Mat) : Array (Array F4) :=
  ((List.finRange 14).map fun i => decRow (A.getD i.val zeroRow)).toArray

@[expose] def decode (A : Mat) : Matrix (Fin 14) (Fin 14) F4 :=
  Matrix.of fun i j => decCode (rowVal (A.getD i.val zeroRow) j.val)

theorem decMat_getD (A : Mat) (i : Fin 14) :
    (decMat A).getD i.val #[] = decRow (A.getD i.val zeroRow) := by
  unfold decMat
  rw [getD_finRange_map]

theorem decode_eq_toMat (A : Mat) : decode A = toMat 14 (decMat A) := by
  ext i j
  rw [decode, Matrix.of_apply, toMat, Matrix.of_apply, decMat_getD, decRow,
    getD_finRange_map]

theorem foldl_congr' {α β : Type*} (l : List α) (f g : β → α → β) (init : β)
    (h : ∀ b a, f b a = g b a) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
      simp only [List.foldl_cons]
      rw [h, ih]

theorem rowVal_xorRow {p q : Row} {j : Nat} (hj : j < 14) :
    rowVal (xorRow p q) j = rowVal p j ^^^ rowVal q j := by
  unfold xorRow canon rowVal
  rw [Nat.testBit_and, Nat.testBit_and, mask14_testBit hj, Bool.and_true, Bool.and_true]
  simp only [Nat.testBit_xor]
  cases p.1.testBit j <;> cases p.2.testBit j <;>
    cases q.1.testBit j <;> cases q.2.testBit j <;> decide

theorem rowVal_foldl_xorRow (l : List Nat) (f : Nat → Row) (init : Row) {j : Nat}
    (hj : j < 14) :
    rowVal (l.foldl (fun p i => xorRow p (f i)) init) j =
      l.foldl (fun acc i => acc ^^^ rowVal (f i) j) (rowVal init j) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldl_cons, List.foldl_cons, ih (init := xorRow init (f a)), rowVal_xorRow hj]

theorem decCode_foldl_xor (l : List Nat) (g : Nat → Nat) (init : Nat)
    (hinit : init < 4) (hg : ∀ i, g i < 4) :
    decCode (l.foldl (fun acc i => acc ^^^ g i) init) =
      l.foldl (fun acc i => acc + decCode (g i)) (decCode init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldl_cons, List.foldl_cons, ← decCode_xor hinit (hg a)]
      exact ih (init := init ^^^ g a) (xor_lt hinit (hg a))

theorem scalarMul_lt {a b : Nat} (ha : a < 4) (hb : b < 4) : scalarMul a b < 4 := by
  interval_cases a <;> interval_cases b <;> decide

theorem foldl_add_range {M : Type*} [AddCommMonoid M] (f : Nat → M) (n : Nat) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
      simp

theorem rowVal_mulRow (a : Row) (B : Mat) {k : Nat} (hk : k < 14) :
    rowVal (mulRow a B) k =
      (List.range 14).foldl (fun acc j => acc ^^^ scalarMul (rowVal a j)
        (rowVal (B.getD j zeroRow) k)) 0 := by
  unfold mulRow
  rw [rowVal_foldl_xorRow _ _ _ hk]
  have hzero : rowVal zeroRow k = 0 := by simp [rowVal, zeroRow]
  rw [hzero]
  refine foldl_congr' _ _ _ _ (fun acc j => ?_)
  rw [rowVal_scale hk]

theorem decCode_rowVal_mulRow (a : Row) (B : Mat) {k : Nat} (hk : k < 14) :
    decCode (rowVal (mulRow a B) k) =
      (List.range 14).foldl (fun acc j => acc + decCode (rowVal a j) *
        decCode (rowVal (B.getD j zeroRow) k)) 0 := by
  rw [rowVal_mulRow a B hk]
  rw [decCode_foldl_xor (l := List.range 14)
    (g := fun j => scalarMul (rowVal a j) (rowVal (B.getD j zeroRow) k))
    (init := 0) (by decide)
    (fun j => scalarMul_lt (rowVal_lt a j) (rowVal_lt (B.getD j zeroRow) k))]
  rw [foldl_congr' _ _ _ _ (fun acc j => by
    rw [decCode_scalarMul (rowVal_lt a j) (rowVal_lt (B.getD j zeroRow) k)])]
  rw [show decCode 0 = 0 from rfl]

theorem getD_mulN (A B : Mat) (i : Fin 14) :
    (mulN A B).getD i.val zeroRow = mulRow (A.getD i.val zeroRow) B := by
  unfold mulN
  rw [getD_finRange_map]

theorem decode_mulN (A B : Mat) : decode (mulN A B) = decode A * decode B := by
  ext i k
  rw [Matrix.mul_apply, decode, Matrix.of_apply, getD_mulN,
    decCode_rowVal_mulRow (A.getD i.val zeroRow) B k.isLt]
  simp only [decode, Matrix.of_apply]
  rw [foldl_add_range (fun j => decCode (rowVal (A.getD i.val zeroRow) j) *
    decCode (rowVal (B.getD j zeroRow) k.val)) 14]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dif_pos (Finset.mem_range.mp hj)]

theorem rowVal_oneM (i j : Nat) (hj : j < 14) :
    rowVal (oneM.getD i zeroRow) j = if j = i then 1 else 0 := by
  unfold oneM
  by_cases hi : i < 14
  · rw [getD_finRange_map (f := fun i : Fin 14 => (1 <<< i.val, 0)) (i := ⟨i, hi⟩)
      (d := zeroRow)]
    have hrow : (1 <<< i : Nat) = 2 ^ i := by simp [Nat.shiftLeft_eq]
    rw [rowVal, hrow]
    by_cases h : j = i
    · subst h
      simp [Nat.testBit_two_pow]
    · have hne : i ≠ j := fun h' => h h'.symm
      simp [h, Nat.testBit_two_pow, hne]
  · have hne : j ≠ i := by omega
    have hnone : (List.finRange 14)[i]? = none := List.getElem?_eq_none (by simp; omega)
    simp [oneM, rowVal, zeroRow, hne, hnone]

theorem decCode_zero : decCode 0 = 0 := rfl

theorem decCode_one : decCode 1 = 1 := rfl

theorem decode_oneM : decode oneM = 1 := by
  ext i j
  rw [decode, Matrix.of_apply, Matrix.one_apply, rowVal_oneM i.val j.val j.isLt]
  by_cases h : i = j
  · have hji : j.val = i.val := by rw [h]
    rw [if_pos hji, if_pos h, decCode_one]
  · have hji : j.val ≠ i.val := fun hv => h (Fin.ext hv.symm)
    rw [if_neg hji, if_neg h, decCode_zero]

theorem decode_eq_of_matEq {A B : Mat} (h : matEq A B = true) : decode A = decode B := by
  have hAB : A = B := beq_iff_eq.mp (by simpa [matEq] using h)
  rw [hAB]

theorem matEq_of_decode_eq {A B : Mat} (hA : A.size = 14) (hB : B.size = 14)
    (hbA : BoundedMat A) (hbB : BoundedMat B) (h : decode A = decode B) :
    matEq A B = true := by
  have hrow : ∀ i < 14, A.getD i zeroRow = B.getD i zeroRow := by
    intro i hi
    have hdec : ∀ j < 14, decCode (rowVal (A.getD i zeroRow) j) =
        decCode (rowVal (B.getD i zeroRow) j) := by
      intro j hj
      have := congrArg (fun M : Matrix (Fin 14) (Fin 14) F4 => M ⟨i, hi⟩ ⟨j, hj⟩) h
      simpa [decode, Matrix.of_apply] using this
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < 14
      · have := decCode_inj (rowVal_lt (A.getD i zeroRow) j)
          (rowVal_lt (B.getD i zeroRow) j) (hdec j hj)
        exact (bits_of_rowVal_eq this).1
      · have h1 : (A.getD i zeroRow).1 < 2 ^ j := by
          have := (hbA i).1
          have hp : 2 ^ 14 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
          omega
        have h2 : (B.getD i zeroRow).1 < 2 ^ j := by
          have := (hbB i).1
          have hp : 2 ^ 14 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
          omega
        rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    · apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < 14
      · have := decCode_inj (rowVal_lt (A.getD i zeroRow) j)
          (rowVal_lt (B.getD i zeroRow) j) (hdec j hj)
        exact (bits_of_rowVal_eq this).2
      · have h1 : (A.getD i zeroRow).2 < 2 ^ j := by
          have := (hbA i).2
          have hp : 2 ^ 14 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
          omega
        have h2 : (B.getD i zeroRow).2 < 2 ^ j := by
          have := (hbB i).2
          have hp : 2 ^ 14 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
          omega
        rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
  have hAB : A = B := by
    apply Array.ext_getElem?
    intro i
    by_cases hi : i < 14
    · rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)]
      congr 1
      rw [Array.getElem_eq_getD, Array.getElem_eq_getD, hrow i hi]
    · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  simp [matEq, hAB]

end CFSG.Quasithin.St84.G24DC.Code
