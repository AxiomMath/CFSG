module

public import CFSG.Fischer.F4
public import CFSG.Quasithin.Vol2.Ch12Sec7ModData
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Fischer

@[expose] def decF (c : ℕ) : F4 := ⟨⟨c % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def decV (v : ℕ) : Fin 3 → F4 := fun i => decF (v >>> (2 * (i : ℕ)))

@[expose] def encV (x : Fin 3 → F4) : ℕ :=
  (x 0).code.val + 4 * (x 1).code.val + 16 * (x 2).code.val

theorem f4_ext {x y : F4} (h : x.code = y.code) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem code_decF (c : ℕ) : (decF c).code.val = c % 4 := rfl

theorem xor_code_lt : ∀ v < 64, ∀ w < 64, ∀ i < 3,
    ((v ^^^ w) >>> (2 * i)) % 4 = ((v >>> (2 * i)) % 4) ^^^ ((w >>> (2 * i)) % 4) := by
  decide +kernel

theorem sV_code_lt : ∀ c < 4, ∀ v < 64, ∀ i < 3,
    ((sV c v) >>> (2 * i)) % 4 =
      (F4.mulCode ⟨c % 4, Nat.mod_lt _ (by norm_num)⟩
        ⟨(v >>> (2 * i)) % 4, Nat.mod_lt _ (by norm_num)⟩).val := by
  decide +kernel

theorem xor_lt_64 : ∀ v < 64, ∀ w < 64, v ^^^ w < 64 := by decide +kernel

theorem sV_lt_64 : ∀ c < 4, ∀ v < 64, sV c v < 64 := by decide +kernel

theorem decV_xor {v w : ℕ} (hv : v < 64) (hw : w < 64) : decV (v ^^^ w) = decV v + decV w := by
  funext i
  apply f4_ext
  apply Fin.ext
  rw [Pi.add_apply, F4.add_def]
  show ((v ^^^ w) >>> (2 * (i : ℕ))) % 4 =
    (((decV v i).code ^^^ (decV w i).code : Fin 4) : ℕ)
  have hx : (((decV v i).code ^^^ (decV w i).code : Fin 4) : ℕ) =
      ((decV v i).code.val ^^^ (decV w i).code.val) % 4 := rfl
  rw [xor_code_lt v hv w hw i i.isLt, hx]
  simp only [decV, code_decF]
  have h1 : (v >>> (2 * (i : ℕ))) % 4 < 2 ^ 2 := Nat.mod_lt _ (by norm_num)
  have h2 : (w >>> (2 * (i : ℕ))) % 4 < 2 ^ 2 := Nat.mod_lt _ (by norm_num)
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow h1 h2)]

theorem decV_sV {c v : ℕ} (hc : c < 4) (hv : v < 64) : decV (sV c v) = decF c • decV v := by
  funext i
  apply f4_ext
  apply Fin.ext
  rw [Pi.smul_apply, smul_eq_mul, F4.mul_def]
  show ((sV c v) >>> (2 * (i : ℕ))) % 4 = (F4.mulCode (decF c).code (decV v i).code : ℕ)
  rw [sV_code_lt c hc v hv i i.isLt]
  rfl

theorem decV_encV (x : Fin 3 → F4) : decV (encV x) = x := by
  have h0 := (x 0).code.isLt
  have h1 := (x 1).code.isLt
  have h2 := (x 2).code.isLt
  funext i
  apply f4_ext
  apply Fin.ext
  simp only [decV, code_decF, encV]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, mul_zero, Nat.shiftRight_zero]
    omega
  · simp only [Fin.mk_one, Fin.isValue, mul_one, Nat.shiftRight_eq_div_pow]
    omega
  · simp only [Fin.reduceFinMk, Fin.isValue, Nat.shiftRight_eq_div_pow]
    omega

theorem encV_lt (x : Fin 3 → F4) : encV x < 64 := by
  have h0 := (x 0).code.isLt
  have h1 := (x 1).code.isLt
  have h2 := (x 2).code.isLt
  simp only [encV]
  omega

theorem encV_decV {v : ℕ} (hv : v < 64) : encV (decV v) = v := by
  simp only [encV, decV, code_decF]
  simp only [Fin.isValue, Fin.val_zero, mul_zero, Fin.val_one, mul_one, Fin.val_two,
    Nat.shiftRight_eq_div_pow]
  omega

namespace Mc

@[expose] def toMat (A : Mc) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of fun i j => decV (![A.c0, A.c1, A.c2] j) i

@[expose] def ofMat (M : Matrix (Fin 3) (Fin 3) F4) : Mc :=
  ⟨encV fun i => M i 0, encV fun i => M i 1, encV fun i => M i 2⟩

theorem and_three_lt (v : ℕ) : v &&& 3 < 4 := by
  have := Nat.and_le_right (n := v) (m := 3)
  omega

theorem decF_and_three (v : ℕ) : decF (v &&& 3) = decF v := by
  simp only [decF]
  congr 2
  have : v &&& 3 = v % 4 := by
    rw [show (3 : ℕ) = 2 ^ 2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  rw [this, Nat.mod_mod]

theorem app_lt (A : Mc) (hA : A.Valid) {v : ℕ} : A.app v < 64 := by
  obtain ⟨h0, h1, h2⟩ := hA
  simp only [app]
  exact xor_lt_64 _ (xor_lt_64 _ (sV_lt_64 _ (and_three_lt v) _ h0) _
    (sV_lt_64 _ (and_three_lt _) _ h1)) _ (sV_lt_64 _ (and_three_lt _) _ h2)

theorem mul_valid {A B : Mc} (hA : A.Valid) : (A.mul B).Valid :=
  ⟨A.app_lt hA, A.app_lt hA, A.app_lt hA⟩

theorem toMat_mulVec (A : Mc) (hA : A.Valid) (v : ℕ) :
    (A.toMat).mulVec (decV v) = decV (A.app v) := by
  obtain ⟨h0, h1, h2⟩ := hA
  have e0 := decV_sV (and_three_lt v) h0
  have e1 := decV_sV (and_three_lt (v >>> 2)) h1
  have e2 := decV_sV (and_three_lt (v >>> 4)) h2
  have s0 := sV_lt_64 _ (and_three_lt v) _ h0
  have s1 := sV_lt_64 _ (and_three_lt (v >>> 2)) _ h1
  have s2 := sV_lt_64 _ (and_three_lt (v >>> 4)) _ h2
  simp only [app]
  rw [decV_xor (xor_lt_64 _ s0 _ s1) s2, decV_xor s0 s1, e0, e1, e2,
    decF_and_three, decF_and_three, decF_and_three]
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, toMat, Matrix.of_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hv1 : v >>> 2 = v >>> (2 * ((1 : Fin 3) : ℕ)) := rfl
  have hv2 : v >>> 4 = v >>> (2 * ((2 : Fin 3) : ℕ)) := rfl
  have hv0 : decF v = decV v 0 := by simp [decV]
  rw [hv1, hv2, hv0]
  simp only [decV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem toMat_apply (A : Mc) (i j : Fin 3) :
    A.toMat i j = decV (![A.c0, A.c1, A.c2] j) i := rfl

theorem toMat_mul (A B : Mc) (hA : A.Valid) (hB : B.Valid) :
    (A.mul B).toMat = A.toMat * B.toMat := by
  obtain ⟨h0, h1, h2⟩ := hB
  ext i j
  have hcol : ∀ k : Fin 3, (fun l => B.toMat l k) = decV (![B.c0, B.c1, B.c2] k) := by
    intro k
    rfl
  have key : (A.toMat * B.toMat) i j = (A.toMat.mulVec (decV (![B.c0, B.c1, B.c2] j))) i := by
    rw [← hcol j]
    rfl
  rw [key, toMat_mulVec A hA]
  fin_cases j <;> rfl

theorem toMat_ofMat (M : Matrix (Fin 3) (Fin 3) F4) : (ofMat M).toMat = M := by
  ext i j
  fin_cases j <;> simp [toMat, ofMat, decV_encV]

theorem ofMat_valid (M : Matrix (Fin 3) (Fin 3) F4) : (ofMat M).Valid :=
  ⟨encV_lt (fun i => M i 0), encV_lt (fun i => M i 1), encV_lt (fun i => M i 2)⟩

theorem ofMat_toMat {A : Mc} (hA : A.Valid) : ofMat A.toMat = A := by
  obtain ⟨h0, h1, h2⟩ := hA
  have e : ∀ k : Fin 3, (fun i => A.toMat i k) = decV (![A.c0, A.c1, A.c2] k) := fun k => rfl
  simp only [ofMat, e]
  simp [encV_decV h0, encV_decV h1, encV_decV h2]

theorem one_valid : one.Valid := by decide

theorem toMat_one : one.toMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pow_valid {A : Mc} (hA : A.Valid) : ∀ n, (A.pow n).Valid
  | 0 => one_valid
  | _ + 1 => mul_valid hA

theorem toMat_pow {A : Mc} (hA : A.Valid) : ∀ n, (A.pow n).toMat = A.toMat ^ n
  | 0 => toMat_one
  | n + 1 => by
    rw [pow, toMat_mul A _ hA (pow_valid hA n), toMat_pow hA n, pow_succ']

end Mc

end CFSG.Quasithin.H13.S127.Mod

end
