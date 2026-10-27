module

public import CFSG.Quasithin.Background.F918U1
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic

public section

namespace CFSG.Quasithin.D35Chk

open scoped Matrix

private theorem testBit_eq_mod (a k : ℕ) : a.testBit k = decide ((a >>> k) % 2 = 1) := by
  rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]

private theorem bit_eq_ite (a k : ℕ) : bit a k = if a.testBit k then 1 else 0 := by
  simp only [bit, Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod, testBit_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one (a >>> k) with h | h <;> simp [h]

theorem bit_le_one (a k : ℕ) : bit a k ≤ 1 := by
  rw [bit_eq_ite]; split <;> decide

private theorem testBit_bit (a k t : ℕ) : (bit a k).testBit t = (decide (t = 0) && a.testBit k) := by
  rw [bit_eq_ite]
  cases a.testBit k
  · simp
  · rcases t with _ | t
    · simp
    · simp [Nat.testBit_add_one]

private theorem testBit_bit_mul (r k x m : ℕ) :
    (bit r k * x).testBit m = (r.testBit k && x.testBit m) := by
  rw [bit_eq_ite]; cases r.testBit k <;> simp

private theorem testBit_shiftLeft_bit (a k s m : ℕ) :
    (Nat.shiftLeft (bit a k) s).testBit m = (decide (s = m) && a.testBit k) := by
  rw [Nat.shiftLeft_eq', Nat.testBit_shiftLeft, testBit_bit, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨by omega, by omega, h3⟩

private theorem testBit_lor (x y i : ℕ) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

private theorem testBit_rowOf (a i j : ℕ) :
    (rowOf a i).testBit j = (a.testBit (5 * i + j) && decide (j < 5)) := by
  simp only [rowOf, Nat.land_eq, Nat.shiftRight_eq', Nat.mul_eq, Nat.testBit_and, Nat.testBit_shiftRight]
  rw [show (31 : ℕ) = 2 ^ 5 - 1 from rfl, Nat.testBit_two_pow_sub_one]

private theorem testBit_vecMul (r b j : ℕ) : (vecMul r b).testBit j =
    (((((r.testBit 0 && (rowOf b 0).testBit j) ^^ (r.testBit 1 && (rowOf b 1).testBit j)) ^^
      (r.testBit 2 && (rowOf b 2).testBit j)) ^^ (r.testBit 3 && (rowOf b 3).testBit j)) ^^
      (r.testBit 4 && (rowOf b 4).testBit j)) := by
  simp only [vecMul, Nat.xor_eq, Nat.mul_eq, Nat.testBit_xor, testBit_bit_mul]

private theorem testBit_bmul (a b : ℕ) {i j : ℕ} (hi : i < 5) (hj : j < 5) :
    (bmul a b).testBit (5 * i + j) =
      (((((a.testBit (5 * i + 0) && b.testBit (5 * 0 + j)) ^^
        (a.testBit (5 * i + 1) && b.testBit (5 * 1 + j))) ^^
        (a.testBit (5 * i + 2) && b.testBit (5 * 2 + j))) ^^
        (a.testBit (5 * i + 3) && b.testBit (5 * 3 + j))) ^^
        (a.testBit (5 * i + 4) && b.testBit (5 * 4 + j))) := by
  rcases i with _ | _ | _ | _ | _ | i <;> rcases j with _ | _ | _ | _ | _ | j <;> (try omega) <;>
    simp [-Nat.testBit_zero, bmul, testBit_vecMul, testBit_rowOf]

private theorem ite_xor_zmod (x y : Bool) :
    (if (x ^^ y) = true then (1 : ZMod 2) else 0) =
      (if x = true then 1 else 0) + (if y = true then 1 else 0) := by
  cases x <;> cases y <;> decide

private theorem ite_and_zmod (x y : Bool) :
    (if (x && y) = true then (1 : ZMod 2) else 0) =
      (if x = true then 1 else 0) * (if y = true then 1 else 0) := by
  cases x <;> cases y <;> decide

theorem bm_xor (a b : ℕ) : bm (Nat.xor a b) = bm a + bm b := by
  ext i j
  simp only [bm, Nat.xor_eq, Nat.testBit_xor, Matrix.add_apply, ite_xor_zmod]

theorem bm_zero : bm 0 = 0 := by
  ext i j
  simp [bm]

theorem bm_bmul (a b : ℕ) : bm (bmul a b) = bm a * bm b := by
  ext i j
  simp only [bm, Matrix.mul_apply, Fin.sum_univ_five]
  rw [testBit_bmul a b i.2 j.2, ite_xor_zmod, ite_xor_zmod, ite_xor_zmod, ite_xor_zmod,
    ite_and_zmod, ite_and_zmod, ite_and_zmod, ite_and_zmod, ite_and_zmod]
  rfl

private theorem testBit_foldl_bit (a : ℕ) (h s : ℕ → ℕ) (init n m : ℕ) :
    ((List.range n).foldl (fun acc q => Nat.lor acc (Nat.shiftLeft (bit a (h q)) (s q))) init).testBit m
        = true ↔
      (init.testBit m = true ∨ ∃ q < n, s q = m ∧ a.testBit (h q) = true) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, testBit_lor,
      Bool.or_eq_true, ih, testBit_shiftLeft_bit, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((h0 | ⟨q, hq, h1⟩) | h2)
      · exact Or.inl h0
      · exact Or.inr ⟨q, by omega, h1⟩
      · exact Or.inr ⟨n, by omega, h2⟩
    · rintro (h0 | ⟨q, hq, h1⟩)
      · exact Or.inl (Or.inl h0)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
        · exact Or.inl (Or.inr ⟨q, hq, h1⟩)
        · exact Or.inr h1

private theorem testBit_bT (a m : ℕ) :
    (bT a).testBit m = (decide (m < 25) && a.testBit (5 * (m % 5) + m / 5)) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq]
  unfold bT
  rw [testBit_foldl_bit]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨q, hq, rfl, h⟩; exact ⟨hq, h⟩
  · rintro ⟨hm, h⟩; exact ⟨m, hm, rfl, h⟩

private theorem testBit_bT_of_lt (a : ℕ) {i j : ℕ} (hi : i < 5) (hj : j < 5) :
    (bT a).testBit (5 * i + j) = a.testBit (5 * j + i) := by
  rw [testBit_bT]
  have h1 : (5 * i + j) % 5 = j := by omega
  have h2 : (5 * i + j) / 5 = i := by omega
  rw [h1, h2, decide_eq_true (by omega : 5 * i + j < 25), Bool.true_and]

theorem bm_bT (a : ℕ) : bm (bT a) = (bm a)ᵀ := by
  ext i j
  simp only [bm, Matrix.transpose_apply, testBit_bT_of_lt a i.2 j.2]

private theorem testBit_idm {i j : ℕ} (hi : i < 5) (hj : j < 5) :
    idm.testBit (5 * i + j) = decide (i = j) := by
  have key : ∀ i < 5, ∀ j < 5, idm.testBit (5 * i + j) = decide (i = j) := by decide
  exact key i hi j hj

theorem bm_idm : bm idm = 1 := by
  ext i j
  simp only [bm, testBit_idm i.2 j.2, Matrix.one_apply, decide_eq_true_eq, Fin.val_inj]

theorem bm_inj {a b : ℕ} (ha : a < 2 ^ 25) (hb : b < 2 ^ 25) (h : bm a = bm b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rcases Nat.lt_or_ge k 25 with hk | hk
  · have e := congrFun (congrFun h ⟨k / 5, by omega⟩) ⟨k % 5, by omega⟩
    simp only [bm, Nat.div_add_mod] at e
    revert e
    cases a.testBit k <;> cases b.testBit k <;> decide
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hk)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hk))]

private theorem lor_lt {x y N : ℕ} (hx : x < 2 ^ N) (hy : y < 2 ^ N) : Nat.lor x y < 2 ^ N :=
  Nat.or_lt_two_pow hx hy

private theorem xor_lt {x y N : ℕ} (hx : x < 2 ^ N) (hy : y < 2 ^ N) : Nat.xor x y < 2 ^ N :=
  Nat.xor_lt_two_pow hx hy

private theorem shiftLeft_lt {x n s N : ℕ} (hx : x < 2 ^ n) (h : n + s ≤ N) :
    Nat.shiftLeft x s < 2 ^ N := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  calc x * 2 ^ s < 2 ^ n * 2 ^ s := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos s)
    _ = 2 ^ (n + s) := (Nat.pow_add 2 n s).symm
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by decide) h

private theorem bit_mul_le (c p x : ℕ) : Nat.mul (bit c p) x ≤ x := by
  have := Nat.mul_le_mul_right x (bit_le_one c p)
  rwa [Nat.one_mul] at this

private theorem rowOf_lt (a i : ℕ) : rowOf a i < 2 ^ 5 := by
  unfold rowOf
  simp only [Nat.land_eq]
  exact Nat.and_lt_two_pow _ (by decide)

private theorem vecMul_lt (r b : ℕ) : vecMul r b < 2 ^ 5 := by
  have h : ∀ k, Nat.mul (bit r k) (rowOf b k) < 2 ^ 5 := fun k =>
    Nat.lt_of_le_of_lt (bit_mul_le r k _) (rowOf_lt b k)
  exact xor_lt (xor_lt (xor_lt (xor_lt (h 0) (h 1)) (h 2)) (h 3)) (h 4)

theorem bmul_lt (a b : ℕ) : bmul a b < 2 ^ 25 := by
  have h := fun i => vecMul_lt (rowOf a i) b
  exact lor_lt (lor_lt (lor_lt (lor_lt
    (Nat.lt_of_lt_of_le (h 0) (Nat.pow_le_pow_right (by decide) (by decide)))
    (shiftLeft_lt (h 1) (by decide))) (shiftLeft_lt (h 2) (by decide)))
    (shiftLeft_lt (h 3) (by decide))) (shiftLeft_lt (h 4) (by decide))

theorem idm_lt : idm < 2 ^ 25 := by decide

private theorem foldl_lt {f : ℕ → ℕ → ℕ} {N : ℕ} (hf : ∀ acc x, acc < N → f acc x < N) :
    ∀ (l : List ℕ) (init : ℕ), init < N → l.foldl f init < N
  | [], _, h => h
  | x :: l, init, h => foldl_lt hf l (f init x) (hf init x h)

private theorem getD_of_ge {l : List ℕ} {p : ℕ} (h : l.length ≤ p) : l.getD p 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

private theorem upos_getD_lt (p : ℕ) : upos.getD p 0 < 25 := by
  rcases Nat.lt_or_ge p 10 with hp | hp
  · have key : ∀ p < 10, upos.getD p 0 < 25 := by decide
    exact key p hp
  · rw [getD_of_ge (by simpa [upos] using hp)]; decide

private theorem lpos_getD_lt (p : ℕ) : lpos.getD p 0 < 25 := by
  rcases Nat.lt_or_ge p 10 with hp | hp
  · have key : ∀ p < 10, lpos.getD p 0 < 25 := by decide
    exact key p hp
  · rw [getD_of_ge (by simpa [lpos] using hp)]; decide

theorem upE_lt (p : ℕ) : upE p < 2 ^ 25 :=
  shiftLeft_lt (n := 1) (by decide) (by have := upos_getD_lt p; omega)

theorem altE_lt (p : ℕ) : altE p < 2 ^ 25 :=
  lor_lt (upE_lt p) (shiftLeft_lt (n := 1) (by decide) (by have := lpos_getD_lt p; omega))

theorem colSum_lt {col : ℕ → ℕ} (h : ∀ p, col p < 2 ^ 25) (c : ℕ) : colSum col c < 2 ^ 25 := by
  unfold colSum
  refine foldl_lt (fun acc p hacc => ?_) _ _ (Nat.two_pow_pos 25)
  exact xor_lt hacc (Nat.lt_of_le_of_lt (bit_mul_le c p (col p)) (h p))

private theorem bm_bit_mul (c p x : ℕ) :
    bm (Nat.mul (bit c p) x) = ((bit c p : ℕ) : ZMod 2) • bm x := by
  rcases (by have := bit_le_one c p; omega : bit c p = 0 ∨ bit c p = 1) with h | h
  · rw [h, Nat.mul_eq, Nat.zero_mul, bm_zero, Nat.cast_zero, zero_smul]
  · rw [h, Nat.mul_eq, Nat.one_mul, Nat.cast_one, one_smul]

private theorem bm_foldl_colSum (col : ℕ → ℕ) (c init n : ℕ) :
    bm ((List.range n).foldl (fun acc p => Nat.xor acc (Nat.mul (bit c p) (col p))) init) =
      bm init + ∑ p ∈ Finset.range n, ((bit c p : ℕ) : ZMod 2) • bm (col p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [bm_xor, ih, bm_bit_mul, Finset.sum_range_succ, add_assoc]

theorem bm_colSum (col : ℕ → ℕ) (c : ℕ) :
    bm (colSum col c) = ∑ p ∈ Finset.range 10, ((bit c p : ℕ) : ZMod 2) • bm (col p) := by
  rw [colSum, bm_foldl_colSum, bm_zero, zero_add]

private theorem val_upI (p : ℕ) : (upI p : ℕ) = upos.getD p 0 / 5 := by
  have := upos_getD_lt p
  simp only [upI, Fin.val_ofNat]
  omega

private theorem val_upJ (p : ℕ) : (upJ p : ℕ) = upos.getD p 0 % 5 := by
  simp only [upJ, Fin.val_ofNat, Nat.mod_mod]

private theorem lpos_getD_eq (p : ℕ) :
    lpos.getD p 0 = 5 * (upos.getD p 0 % 5) + upos.getD p 0 / 5 := by
  rcases Nat.lt_or_ge p 10 with hp | hp
  · have key : ∀ p < 10, lpos.getD p 0 = 5 * (upos.getD p 0 % 5) + upos.getD p 0 / 5 := by decide
    exact key p hp
  · rw [getD_of_ge (by simpa [lpos] using hp), getD_of_ge (by simpa [upos] using hp)]

private theorem upos_eq_iff (q : ℕ) (i j : Fin 5) :
    upos.getD q 0 = 5 * (i : ℕ) + j ↔ i = upI q ∧ j = upJ q := by
  rw [Fin.ext_iff, Fin.ext_iff, val_upI, val_upJ]
  have := i.2; have := j.2; have := upos_getD_lt q
  constructor
  · intro h; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; omega

private theorem lpos_eq_iff (q : ℕ) (i j : Fin 5) :
    lpos.getD q 0 = 5 * (i : ℕ) + j ↔ i = upJ q ∧ j = upI q := by
  rw [lpos_getD_eq, Fin.ext_iff, Fin.ext_iff, val_upI, val_upJ]
  have := i.2; have := j.2; have := upos_getD_lt q
  constructor
  · intro h; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; omega

private theorem upI_lt_upJ {p : ℕ} (hp : p < 10) : (upI p : ℕ) < upJ p := by
  rw [val_upI, val_upJ]
  have key : ∀ p < 10, upos.getD p 0 / 5 < upos.getD p 0 % 5 := by decide
  exact key p hp

private theorem upos_inj {p q : ℕ} (hp : p < 10) (hq : q < 10) (h : upos.getD p 0 = upos.getD q 0) :
    p = q := by
  have key : ∀ p < 10, ∀ q < 10, upos.getD p 0 = upos.getD q 0 → p = q := by decide
  exact key p hp q hq h

private theorem upIJ_inj {p q : ℕ} (hp : p < 10) (hq : q < 10) (h1 : upI p = upI q)
    (h2 : upJ p = upJ q) : p = q := by
  apply upos_inj hp hq
  have e1 := congrArg Fin.val h1
  have e2 := congrArg Fin.val h2
  simp only [val_upI, val_upJ] at e1 e2
  have := upos_getD_lt p; have := upos_getD_lt q
  omega

private theorem testBit_upE (q m : ℕ) : (upE q).testBit m = decide (upos.getD q 0 = m) := by
  simp only [upE, Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.testBit_two_pow]

private theorem bm_upE (q : ℕ) (i j : Fin 5) :
    bm (upE q) i j = if i = upI q ∧ j = upJ q then 1 else 0 := by
  simp only [bm, testBit_upE, decide_eq_true_eq, upos_eq_iff]

private theorem bm_altE (q : ℕ) (i j : Fin 5) :
    bm (altE q) i j = if (i = upI q ∧ j = upJ q) ∨ (i = upJ q ∧ j = upI q) then 1 else 0 := by
  simp only [bm, altE, testBit_lor, testBit_upE, Nat.shiftLeft_eq', Nat.one_shiftLeft,
    Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, upos_eq_iff, lpos_eq_iff]

theorem bm_upSum_upper (c : ℕ) {p : ℕ} (hp : p < 10) :
    bm (upSum c) (upI p) (upJ p) = ((bit c p : ℕ) : ZMod 2) := by
  rw [upSum, bm_colSum, Matrix.sum_apply, Finset.sum_eq_single p]
  · rw [Matrix.smul_apply, bm_upE, ite_eq_left ⟨rfl, rfl⟩, smul_eq_mul, mul_one]
  · intro q hq hqp
    rw [Matrix.smul_apply, bm_upE, ite_eq_right, smul_zero]
    rintro ⟨h1, h2⟩
    exact hqp (upIJ_inj (Finset.mem_range.1 hq) hp h1.symm h2.symm)
  · intro h; exact absurd (Finset.mem_range.2 hp) h

theorem bm_upSum_eq_zero (c : ℕ) {i j : Fin 5} (h : ∀ p < 10, ¬ (i = upI p ∧ j = upJ p)) :
    bm (upSum c) i j = 0 := by
  rw [upSum, bm_colSum, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Matrix.smul_apply, bm_upE, ite_eq_right (h q (Finset.mem_range.1 hq)), smul_zero]

theorem bm_altSum_upper (c : ℕ) {p : ℕ} (hp : p < 10) :
    bm (altSum c) (upI p) (upJ p) = ((bit c p : ℕ) : ZMod 2) := by
  rw [altSum, bm_colSum, Matrix.sum_apply, Finset.sum_eq_single p]
  · rw [Matrix.smul_apply, bm_altE, ite_eq_left (Or.inl ⟨rfl, rfl⟩), smul_eq_mul, mul_one]
  · intro q hq hqp
    have hq' := Finset.mem_range.1 hq
    rw [Matrix.smul_apply, bm_altE, ite_eq_right, smul_zero]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hqp (upIJ_inj hq' hp h1.symm h2.symm)
    · have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      have := upI_lt_upJ hp
      have := upI_lt_upJ hq'
      omega
  · intro h; exact absurd (Finset.mem_range.2 hp) h

theorem bm_altSum_lower (c : ℕ) {p : ℕ} (hp : p < 10) :
    bm (altSum c) (upJ p) (upI p) = ((bit c p : ℕ) : ZMod 2) := by
  rw [altSum, bm_colSum, Matrix.sum_apply, Finset.sum_eq_single p]
  · rw [Matrix.smul_apply, bm_altE, ite_eq_left (Or.inr ⟨rfl, rfl⟩), smul_eq_mul, mul_one]
  · intro q hq hqp
    have hq' := Finset.mem_range.1 hq
    rw [Matrix.smul_apply, bm_altE, ite_eq_right, smul_zero]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      have := upI_lt_upJ hp
      have := upI_lt_upJ hq'
      omega
    · exact hqp (upIJ_inj hq' hp h2.symm h1.symm)
  · intro h; exact absurd (Finset.mem_range.2 hp) h

theorem bm_altSum_diag (c : ℕ) (i : Fin 5) : bm (altSum c) i i = 0 := by
  rw [altSum, bm_colSum, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun q hq => ?_
  have := upI_lt_upJ (Finset.mem_range.1 hq)
  rw [Matrix.smul_apply, bm_altE, ite_eq_right, smul_zero]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · rw [← h1, ← h2] at this; exact Nat.lt_irrefl _ this
  · rw [← h1, ← h2] at this; exact Nat.lt_irrefl _ this

private theorem testBit_unitri (c m : ℕ) : (unitri c).testBit m = true ↔
    idm.testBit m = true ∨ ∃ q < 10, upos.getD q 0 = m ∧ c.testBit q = true :=
  testBit_foldl_bit c (fun q => q) (fun q => upos.getD q 0) idm 10 m

theorem bm_unitri (c : ℕ) : bm (unitri c) = 1 + bm (upSum c) := by
  ext i j
  rw [Matrix.add_apply, Matrix.one_apply]
  by_cases hup : ∃ p < 10, i = upI p ∧ j = upJ p
  · obtain ⟨p, hp, rfl, rfl⟩ := hup
    have hne : upI p ≠ upJ p := fun e => Nat.lt_irrefl _ (e ▸ upI_lt_upJ hp)
    rw [bm_upSum_upper c hp, ite_eq_right hne, zero_add, bit_eq_ite]
    have key : (unitri c).testBit (5 * (upI p : ℕ) + upJ p) = c.testBit p := by
      rw [Bool.eq_iff_iff, testBit_unitri, testBit_idm (upI p).2 (upJ p).2]
      simp only [upos_eq_iff, decide_eq_true_eq, Fin.val_inj]
      constructor
      · rintro (h | ⟨q, hq, ⟨h1, h2⟩, h3⟩)
        · exact absurd h hne
        · rwa [upIJ_inj hp hq h1 h2]
      · intro h; exact Or.inr ⟨p, hp, ⟨rfl, rfl⟩, h⟩
    simp only [bm, key]
    cases c.testBit p <;> simp
  · have hup' : ∀ p < 10, ¬ (i = upI p ∧ j = upJ p) := fun p hp h => hup ⟨p, hp, h⟩
    rw [bm_upSum_eq_zero c hup', add_zero]
    have key : (unitri c).testBit (5 * (i : ℕ) + j) = idm.testBit (5 * i + j) := by
      rw [Bool.eq_iff_iff, testBit_unitri]
      simp only [upos_eq_iff]
      constructor
      · rintro (h | ⟨q, hq, h1, -⟩)
        · exact h
        · exact absurd h1 (hup' q hq)
      · exact Or.inl
    simp only [bm, key, testBit_idm i.2 j.2, decide_eq_true_eq, Fin.val_inj]

theorem bm_colSum_commCol (g c : ℕ) :
    bm (colSum (commCol g) c) = bm (unitri g) * bm (upSum c) + bm (upSum c) * bm (unitri g) := by
  rw [bm_colSum, upSum, bm_colSum, Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [commCol, bm_xor, bm_bmul, bm_bmul, Matrix.mul_smul, Matrix.smul_mul, smul_add]

theorem bm_colSum_fixCol (g c : ℕ) :
    bm (colSum (fixCol g) c) = bm (unitri g) * bm (altSum c) * (bm (unitri g))ᵀ + bm (altSum c) := by
  rw [bm_colSum, altSum, bm_colSum, Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [fixCol, bm_xor, bm_bmul, bm_bmul, bm_bT, Matrix.mul_smul, Matrix.smul_mul, smul_add]

theorem bm_colSum_fixColD (g c : ℕ) :
    bm (colSum (fixColD g) c) = (bm (unitri g))ᵀ * bm (altSum c) * bm (unitri g) + bm (altSum c) := by
  rw [bm_colSum, altSum, bm_colSum, Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [fixColD, bm_xor, bm_bmul, bm_bmul, bm_bT, Matrix.mul_smul, Matrix.smul_mul, smul_add]

end CFSG.Quasithin.D35Chk
