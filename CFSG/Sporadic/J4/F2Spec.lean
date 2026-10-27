module

public import Mathlib
public import Certificates.Data.CFSGNative.J4.F2
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.J4

open CFSG.Sporadic.J4.Native Finset
open scoped Matrix

namespace Native.V2

@[expose] def toVec (a : V2) : Fin 112 → ZMod 2 := fun j => if a.testBit j.val then 1 else 0

@[expose] def toNat (a : V2) : ℕ := a.lo.toNat + 2 ^ 64 * a.hi.toNat

theorem ext_words {a b : V2} (h0 : a.lo = b.lo) (h1 : a.hi = b.hi) : a = b := by
  cases a; cases b; simp_all

theorem testBit_eq_word (a : V2) (j : ℕ) :
    a.testBit j = (a.word (j / 64)).toNat.testBit (j % 64) := by
  unfold testBit
  generalize a.word (j / 64) = w
  have hj : (UInt64.ofNat (j % 64)).toNat % 64 = j % 64 := by
    rw [UInt64.toNat_ofNat']; omega
  rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_shiftRight,
    hj, UInt64.toNat_one, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff,
    Nat.shiftRight_eq_div_pow]

theorem word_xor (a b : V2) (k : ℕ) : (a.xor b).word k = a.word k ^^^ b.word k := by
  unfold word xor; split_ifs <;> rfl

theorem testBit_xor (a b : V2) (j : ℕ) :
    (a.xor b).testBit j = (a.testBit j ^^ b.testBit j) := by
  rw [testBit_eq_word, testBit_eq_word, testBit_eq_word, word_xor, UInt64.toNat_xor,
    Nat.testBit_xor]

theorem zero_testBit (j : ℕ) : zero.testBit j = false := by
  rw [testBit_eq_word]; unfold word zero; split_ifs <;> simp

theorem testBit_toNat (a : V2) {j : ℕ} (hj : j < 128) : a.toNat.testBit j = a.testBit j := by
  rw [toNat, add_comm, testBit_eq_word, Nat.testBit_two_pow_mul_add _ (UInt64.toNat_lt _)]
  split_ifs with h0
  · rw [show j / 64 = 0 by omega, show j % 64 = j by omega]; rfl
  · rw [show j / 64 = 1 by omega, show j % 64 = j - 64 by omega]; rfl

theorem toNat_lt (a : V2) : a.toNat < 2 ^ 128 := by
  have := UInt64.toNat_lt a.lo; have := UInt64.toNat_lt a.hi
  unfold toNat; omega

theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  have := UInt64.toNat_lt a.lo; have := UInt64.toNat_lt a.hi
  have := UInt64.toNat_lt b.lo; have := UInt64.toNat_lt b.hi
  unfold toNat at h
  exact ext_words (UInt64.toNat_inj.1 (by omega)) (UInt64.toNat_inj.1 (by omega))

theorem wf_iff_hi (a : V2) : a.wf = true ↔ a.hi.toNat < 2 ^ 48 := by
  unfold wf
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

theorem wf_iff_toNat_lt (a : V2) : a.wf = true ↔ a.toNat < 2 ^ 112 := by
  have := UInt64.toNat_lt a.lo
  rw [wf_iff_hi]; unfold toNat; omega

theorem wf_iff_testBit (a : V2) :
    a.wf = true ↔ ∀ j, 112 ≤ j → j < 128 → a.testBit j = false := by
  rw [wf_iff_toNat_lt]
  constructor
  · intro h j hj hj'
    rw [← testBit_toNat a hj']
    exact Nat.testBit_lt_two_pow (h.trans_le (Nat.pow_le_pow_right (by norm_num) hj))
  · intro h
    refine Nat.lt_pow_two_of_testBit _ fun j hj => ?_
    by_cases hj' : j < 128
    · rw [testBit_toNat a hj']; exact h j hj hj'
    · exact Nat.testBit_lt_two_pow ((toNat_lt a).trans_le (Nat.pow_le_pow_right (by norm_num)
        (by omega)))

theorem zero_wf : zero.wf = true := by decide

theorem xor_wf {a b : V2} (ha : a.wf = true) (hb : b.wf = true) : (a.xor b).wf = true := by
  rw [wf_iff_testBit] at *
  intro j hj hj'
  rw [testBit_xor, ha j hj hj', hb j hj hj']; rfl

theorem toVec_apply (a : V2) (j : Fin 112) : a.toVec j = if a.testBit j.val then 1 else 0 := rfl

theorem toVec_xor (a b : V2) : (a.xor b).toVec = a.toVec + b.toVec := by
  funext j
  simp only [toVec, testBit_xor, Pi.add_apply]
  cases a.testBit j.val <;> cases b.testBit j.val <;> decide

theorem toVec_zero : zero.toVec = 0 := by
  funext j; simp [toVec, zero_testBit]

theorem testBit_eq_of_toVec_eq {a b : V2} (h : a.toVec = b.toVec) {j : ℕ} (hj : j < 112) :
    a.testBit j = b.testBit j := by
  have := congrFun h ⟨j, hj⟩
  simp only [toVec] at this
  cases ha : a.testBit j <;> cases hb : b.testBit j <;> simp_all

theorem eq_of_toVec_eq {a b : V2} (ha : a.wf = true) (hb : b.wf = true)
    (h : a.toVec = b.toVec) : a = b := by
  apply toNat_injective
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 112
  · rw [testBit_toNat a (by omega), testBit_toNat b (by omega)]
    exact testBit_eq_of_toVec_eq h hj
  · have hle : 2 ^ 112 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (((wf_iff_toNat_lt a).1 ha).trans_le hle),
      Nat.testBit_lt_two_pow (((wf_iff_toNat_lt b).1 hb).trans_le hle)]

theorem toVec_inj {a b : V2} (ha : a.wf = true) (hb : b.wf = true) :
    a.toVec = b.toVec ↔ a = b :=
  ⟨eq_of_toVec_eq ha hb, fun h => h ▸ rfl⟩

theorem beq_iff {a b : V2} : a.beq b = true ↔ a = b := by
  constructor
  · intro h
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
    exact ext_words h.1 h.2
  · rintro rfl; simp [beq]

theorem setBit_testBit (a : V2) {i j : ℕ} (hi : i < 128) (hj : j < 128) :
    (a.setBit j).testBit i = (a.testBit i || decide (i = j)) := by
  have hm : ((1 : UInt64) <<< UInt64.ofNat (j % 64)).toNat = 2 ^ (j % 64) := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_one, UInt64.toNat_ofNat', Nat.one_shiftLeft]
    rw [Nat.mod_eq_of_lt (a := j % 64) (by omega), Nat.mod_eq_of_lt (a := j % 64) (by omega)]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have key : ∀ w : UInt64, (w ||| (1 : UInt64) <<< UInt64.ofNat (j % 64)).toNat.testBit (i % 64) =
      (w.toNat.testBit (i % 64) || decide (j % 64 = i % 64)) := by
    intro w; rw [UInt64.toNat_or, Nat.testBit_or, hm, Nat.testBit_two_pow]
  rw [testBit_eq_word, testBit_eq_word]
  unfold setBit
  obtain hj' | hj' : j / 64 = 0 ∨ j / 64 = 1 := by omega
  all_goals obtain hi' | hi' : i / 64 = 0 ∨ i / 64 = 1 := by omega
  all_goals simp (config := { decide := true }) only [hj', hi', word, key, reduceIte]
  all_goals first
    | (congr 1; simp only [decide_eq_decide]; omega)
    | (have : i ≠ j := by omega
       simp [this])

private theorem foldl_setBit_testBit (f : ℕ → Bool) {n : ℕ} (hn : n ≤ 112) {i : ℕ}
    (hi : i < 128) :
    ((List.range n).foldl (fun v j => if f j then v.setBit j else v) zero).testBit i =
      (decide (i < n) && f i) := by
  induction n with
  | zero => simp [zero_testBit]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h : i = n
    · subst h
      split_ifs with hf
      · rw [setBit_testBit _ hi (by omega)]; simp [hf]
      · rw [ih (by omega)]; simp [hf]
    · have h' : (i < n + 1 ↔ i < n) := by omega
      split_ifs with hf
      · rw [setBit_testBit _ hi (by omega), ih (by omega)]; simp [h, h']
      · rw [ih (by omega)]; simp [h']

theorem ofFn_testBit (f : ℕ → Bool) {j : ℕ} (hj : j < 112) : (ofFn f).testBit j = f j := by
  unfold ofFn; rw [foldl_setBit_testBit f le_rfl (by omega)]; simp [hj]

theorem ofFn_wf (f : ℕ → Bool) : (ofFn f).wf = true := by
  rw [wf_iff_testBit]
  intro j hj hj'
  unfold ofFn; rw [foldl_setBit_testBit f le_rfl hj']; simp; omega

theorem toVec_ofFn (f : ℕ → Bool) (j : Fin 112) :
    (ofFn f).toVec j = if f j.val then 1 else 0 := by
  rw [toVec_apply, ofFn_testBit f j.isLt]

end Native.V2

theorem rows_getD_wf {r : Array V2} (hr : ∀ x ∈ r, x.wf = true) (i : ℕ) :
    (r[i]?.getD V2.zero).wf = true := by
  cases h : r[i]? with
  | none => exact V2.zero_wf
  | some x => exact hr x (Array.mem_of_getElem? h)

private theorem getElem?_ofFn_getD {n : ℕ} (f : Fin n → V2) (i : Fin n) :
    (Array.ofFn f)[i.val]?.getD V2.zero = f i := by
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

private theorem ofFn_wf_of_forall {n : ℕ} {f : Fin n → V2} (hf : ∀ i, (f i).wf = true) :
    ∀ x ∈ Array.ofFn f, x.wf = true := by
  intro x hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact hf i

private theorem foldl_xor_toVec (P : ℕ → Prop) [DecidablePred P] (g : ℕ → V2) (n : ℕ)
    (init : V2) :
    ((List.range n).foldl (fun acc i => if P i then acc.xor (g i) else acc) init).toVec =
      init.toVec + ∑ i ∈ range n, if P i then (g i).toVec else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sum_range_succ,
      ← add_assoc, ← ih]
    split_ifs <;> simp [V2.toVec_xor]

private theorem foldl_xor_wf (P : ℕ → Prop) [DecidablePred P] (g : ℕ → V2)
    (hg : ∀ i, (g i).wf = true) (n : ℕ) {init : V2} (hinit : init.wf = true) :
    ((List.range n).foldl (fun acc i => if P i then acc.xor (g i) else acc) init).wf = true := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split_ifs
    · exact V2.xor_wf ih (hg n)
    · exact ih

theorem frEntry_toVec (rows : Array V2) (K c : ℕ) :
    (frEntry rows K c).toVec =
      ∑ i ∈ range 8, if c.testBit i then (rows[8 * K + i]?.getD V2.zero).toVec else 0 := by
  unfold frEntry
  rw [foldl_xor_toVec, V2.toVec_zero, zero_add]
  refine sum_congr rfl fun i _ => ?_
  have h : ((c >>> i) % 2 = 1) ↔ c.testBit i = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff, Nat.shiftRight_eq_div_pow]
  exact if_congr h rfl rfl

theorem frEntry_wf {rows : Array V2} (hrows : ∀ x ∈ rows, x.wf = true) (K c : ℕ) :
    (frEntry rows K c).wf = true := by
  unfold frEntry
  exact foldl_xor_wf _ _ (fun i => rows_getD_wf hrows _) _ V2.zero_wf

theorem frTable_size (rows : Array V2) : (frTable rows).size = 14 * 256 := by
  unfold frTable; exact Array.size_ofFn

theorem frTable_getElem! (rows : Array V2) {n : ℕ} (hn : n < 14 * 256) :
    (frTable rows)[n]! = frEntry rows (n / 256) (n % 256) := by
  rw [getElem!_pos (frTable rows) n (by rw [frTable_size]; exact hn)]
  unfold frTable
  rw [Array.getElem_ofFn]

private theorem byte_toNat (w s : UInt64) :
    ((w >>> s) &&& 0xFF).toNat = w.toNat >>> (s.toNat % 64) % 256 := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, show (0xFF : UInt64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem frByte_eq (rows : Array V2) {base : ℕ} (hb : base % 256 = 0) (hlt : base < 14 * 256)
    (w s : UInt64) (acc : V2) :
    frByte (frTable rows) base w s acc =
      acc.xor (frEntry rows (base / 256) (w.toNat >>> (s.toNat % 64) % 256)) := by
  unfold frByte
  rw [byte_toNat]
  generalize w.toNat >>> (s.toNat % 64) = x
  have hx := Nat.mod_lt x (show 256 > 0 by norm_num)
  rw [frTable_getElem! rows (by omega)]
  congr 2 <;> omega

theorem frByte_toVec (rows : Array V2) {base : ℕ} (hb : base % 256 = 0) (hlt : base < 14 * 256)
    (w s : UInt64) (acc : V2) :
    (frByte (frTable rows) base w s acc).toVec = acc.toVec + ∑ i ∈ range 8,
      if w.toNat.testBit (s.toNat % 64 + i) then
        (rows[8 * (base / 256) + i]?.getD V2.zero).toVec else 0 := by
  rw [frByte_eq rows hb hlt, V2.toVec_xor, frEntry_toVec]
  refine congrArg (acc.toVec + ·) ?_
  refine sum_congr rfl fun i hi => ?_
  have h : ∀ x : ℕ, (x % 256).testBit i = (decide (i < 8) && x.testBit i) :=
    fun x => Nat.testBit_mod_two_pow x 8 i
  rw [h, Nat.testBit_shiftRight]
  simp [mem_range.1 hi]

theorem frByte_wf {rows : Array V2} (hrows : ∀ x ∈ rows, x.wf = true) {base : ℕ}
    (hb : base % 256 = 0) (hlt : base < 14 * 256) (w s : UInt64) {acc : V2}
    (hacc : acc.wf = true) : (frByte (frTable rows) base w s acc).wf = true := by
  rw [frByte_eq rows hb hlt]; exact V2.xor_wf hacc (frEntry_wf hrows _ _)

private theorem frWord_eq_foldl (t : Array V2) (base : ℕ) (w : UInt64) (acc : V2) :
    frWord t base w acc =
      (List.range 8).foldl (fun acc b => frByte t (base + 256 * b) w (UInt64.ofNat (8 * b)) acc)
        acc := by
  unfold frWord; rfl

private theorem frWord6_eq_foldl (t : Array V2) (base : ℕ) (w : UInt64) (acc : V2) :
    frWord6 t base w acc =
      (List.range 6).foldl (fun acc b => frByte t (base + 256 * b) w (UInt64.ofNat (8 * b)) acc)
        acc := by
  unfold frWord6; rfl

private theorem foldl_frByte_toVec (rows : Array V2) {base : ℕ} (hb : base % 256 = 0)
    (w : UInt64) {n : ℕ} (hn : n ≤ 8) (hlt : base + 256 * n ≤ 14 * 256) (acc : V2) :
    ((List.range n).foldl
        (fun acc b => frByte (frTable rows) (base + 256 * b) w (UInt64.ofNat (8 * b)) acc)
        acc).toVec =
      acc.toVec + ∑ b ∈ range n, ∑ i ∈ range 8, if w.toNat.testBit (8 * b + i) then
        (rows[8 * (base / 256 + b) + i]?.getD V2.zero).toVec else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      frByte_toVec rows (by omega) (by omega), ih (by omega) (by omega), add_assoc]
    conv_rhs => rw [sum_range_succ]
    have h1 : (UInt64.ofNat (8 * n)).toNat % 64 = 8 * n := by
      rw [UInt64.toNat_ofNat']; omega
    have h2 : (base + 256 * n) / 256 = base / 256 + n := by omega
    rw [h1, h2]

private theorem foldl_frByte_wf {rows : Array V2} (hrows : ∀ x ∈ rows, x.wf = true) {base : ℕ}
    (hb : base % 256 = 0) (w : UInt64) {n : ℕ} (hlt : base + 256 * n ≤ 14 * 256) {acc : V2}
    (hacc : acc.wf = true) :
    ((List.range n).foldl
        (fun acc b => frByte (frTable rows) (base + 256 * b) w (UInt64.ofNat (8 * b)) acc)
        acc).wf = true := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact frByte_wf hrows (by omega) (by omega) _ _ (ih (by omega))

private theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n a b : ℕ}
    (h : n = b * a) : ∑ j ∈ range n, f j = ∑ i ∈ range a, ∑ j ∈ range b, f (b * i + j) := by
  subst h
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

theorem frWord_toVec (rows : Array V2) (v : V2) (acc : V2) :
    (frWord (frTable rows) 0 v.lo acc).toVec = acc.toVec + ∑ m ∈ range 64,
      if v.testBit m then (rows[m]?.getD V2.zero).toVec else 0 := by
  rw [frWord_eq_foldl, foldl_frByte_toVec rows (by omega) _ (le_refl 8) (by omega),
    sum_range_mul_eq _ (show 64 = 8 * 8 by norm_num)]
  refine congrArg (acc.toVec + ·) ?_
  refine sum_congr rfl fun b hb => sum_congr rfl fun i hi => ?_
  rw [mem_range] at hb hi
  refine if_congr ?_ (by rw [show 8 * (0 / 256 + b) + i = 8 * b + i by omega]) rfl
  rw [V2.testBit_eq_word, show (8 * b + i) / 64 = 0 by omega,
    show (8 * b + i) % 64 = 8 * b + i by omega]
  rfl

theorem frWord6_toVec (rows : Array V2) (v : V2) (acc : V2) :
    (frWord6 (frTable rows) 2048 v.hi acc).toVec = acc.toVec + ∑ m ∈ range 48,
      if v.testBit (64 + m) then (rows[64 + m]?.getD V2.zero).toVec else 0 := by
  rw [frWord6_eq_foldl, foldl_frByte_toVec rows (by omega) _ (by omega) (by omega),
    sum_range_mul_eq _ (show 48 = 8 * 6 by norm_num)]
  refine congrArg (acc.toVec + ·) ?_
  refine sum_congr rfl fun b hb => sum_congr rfl fun i hi => ?_
  rw [mem_range] at hb hi
  refine if_congr ?_ (by rw [show 8 * (2048 / 256 + b) + i = 64 + (8 * b + i) by omega]) rfl
  rw [V2.testBit_eq_word, show (64 + (8 * b + i)) / 64 = 1 by omega,
    show (64 + (8 * b + i)) % 64 = 8 * b + i by omega]
  rfl

theorem frApply_frTable_toVec_eq_sum (rows : Array V2) (v : V2) :
    (frApply (frTable rows) v).toVec =
      ∑ j ∈ range 112, if v.testBit j then (rows[j]?.getD V2.zero).toVec else 0 := by
  unfold frApply
  rw [frWord6_toVec, frWord_toVec, V2.toVec_zero, zero_add,
    show range 112 = range (64 + 48) from rfl, sum_range_add]

theorem frApply_frTable_toVec (rows : Array V2) (v : V2) :
    (frApply (frTable rows) v).toVec =
      fun i => ∑ j : Fin 112, v.toVec j * (rows[j.val]?.getD V2.zero).toVec i := by
  rw [frApply_frTable_toVec_eq_sum]
  funext i
  rw [Finset.sum_apply, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  rw [V2.toVec_apply]
  split_ifs <;> simp

theorem frApply_frTable_wf {rows : Array V2} (hrows : ∀ x ∈ rows, x.wf = true) (v : V2) :
    (frApply (frTable rows) v).wf = true := by
  unfold frApply
  rw [frWord6_eq_foldl, frWord_eq_foldl]
  refine foldl_frByte_wf hrows (by norm_num) _ (by norm_num) ?_
  exact foldl_frByte_wf hrows (by norm_num) _ (by norm_num) V2.zero_wf

@[expose] def rowsMatrix (r : Array V2) : Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  Matrix.of fun i j => (r[i.val]?.getD V2.zero).toVec j

theorem rowsMatrix_apply (r : Array V2) (i j : Fin 112) :
    rowsMatrix r i j = (r[i.val]?.getD V2.zero).toVec j := rfl

theorem frApply_toVec_eq_vecMul (r : Array V2) (v : V2) :
    (frApply (frTable r) v).toVec = v.toVec ᵥ* rowsMatrix r := by
  rw [frApply_frTable_toVec]
  funext i
  simp only [Matrix.vecMul, dotProduct, rowsMatrix_apply]

theorem wsChar_eq_asciiWhitespace :
    CFSG.Sporadic.Th.Native.wsChar = CFSG.Blueprint.NativeSporadic.asciiWhitespace := by
  funext c; unfold CFSG.Sporadic.Th.Native.wsChar; rfl

theorem decode_apply_eq_decodeEntries (s : String) (i j : Fin 112) :
    CFSG.Blueprint.NativeSporadic.decode 2 112 1 s i j =
      (((CFSG.Sporadic.Th.Native.decodeEntries s)[i.val * 112 + j.val]?.getD 0 : ℕ) : ZMod 2) := by
  unfold CFSG.Sporadic.Th.Native.decodeEntries
  rw [wsChar_eq_asciiWhitespace]
  rfl

private theorem natCast_zmod_two (n : ℕ) :
    (n : ZMod 2) = if (n % 2 == 1) = true then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem rowsOf_size (s : String) : (rowsOf s).size = 112 := by
  unfold rowsOf; exact Array.size_ofFn

theorem rowsOf_wf (s : String) : ∀ x ∈ rowsOf s, x.wf = true := by
  unfold rowsOf; exact ofFn_wf_of_forall fun _ => V2.ofFn_wf _

theorem rowsMatrix_rowsOf (s : String) :
    rowsMatrix (rowsOf s) = CFSG.Blueprint.NativeSporadic.decode 2 112 1 s := by
  ext i j
  rw [decode_apply_eq_decodeEntries, rowsMatrix_apply]
  unfold rowsOf
  rw [getElem?_ofFn_getD]
  unfold rowOfEntries
  rw [V2.toVec_ofFn, List.getElem?_toArray, natCast_zmod_two]

theorem transposeRows_wf (r : Array V2) : ∀ x ∈ transposeRows r, x.wf = true := by
  unfold transposeRows; exact ofFn_wf_of_forall fun _ => V2.ofFn_wf _

theorem rowsMatrix_transposeRows (r : Array V2) :
    rowsMatrix (transposeRows r) = (rowsMatrix r)ᵀ := by
  ext j i
  rw [Matrix.transpose_apply, rowsMatrix_apply, rowsMatrix_apply]
  unfold transposeRows
  rw [getElem?_ofFn_getD, V2.toVec_ofFn, V2.toVec_apply]

theorem mulRows_size (X Y : Array V2) : (mulRows X Y).size = X.size := by
  unfold mulRows; exact Array.size_map

theorem mulRows_wf (X : Array V2) {Y : Array V2} (hY : ∀ y ∈ Y, y.wf = true) :
    ∀ z ∈ mulRows X Y, z.wf = true := by
  intro z hz
  unfold mulRows at hz
  obtain ⟨x, -, rfl⟩ := Array.mem_map.1 hz
  exact frApply_frTable_wf hY x

theorem rowsMatrix_mulRows (X Y : Array V2) :
    rowsMatrix (mulRows X Y) = rowsMatrix X * rowsMatrix Y := by
  ext i k
  rw [Matrix.mul_apply, rowsMatrix_apply]
  unfold mulRows
  rw [Array.getElem?_map]
  simp only [rowsMatrix_apply]
  cases X[i.val]? with
  | none => simp [V2.toVec_zero]
  | some x =>
    rw [Option.map_some, Option.getD_some, Option.getD_some, frApply_frTable_toVec]

theorem idRows_size : idRows.size = 112 := by
  unfold idRows; exact Array.size_ofFn

theorem idRows_wf : ∀ x ∈ idRows, x.wf = true := by
  unfold idRows; exact ofFn_wf_of_forall fun _ => V2.ofFn_wf _

theorem rowsMatrix_idRows : rowsMatrix idRows = 1 := by
  ext i j
  rw [rowsMatrix_apply, Matrix.one_apply]
  unfold idRows
  rw [getElem?_ofFn_getD, V2.toVec_ofFn]
  by_cases h : i = j
  · subst h; simp
  · have h' : j.val ≠ i.val := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem eqRows_iff {X Y : Array V2} : eqRows X Y = true ↔ X = Y := by
  constructor
  · intro h
    unfold eqRows at h
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨hs, h⟩ := h
    refine Array.ext hs fun i h1 h2 => ?_
    have := V2.beq_iff.1 (h i (List.mem_range.2 h1))
    rwa [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some,
      Option.getD_some] at this
  · rintro rfl
    unfold eqRows
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    exact ⟨rfl, fun i _ => V2.beq_iff.2 rfl⟩

theorem rowsMatrix_eq_of_eqRows {X Y : Array V2} (h : eqRows X Y = true) :
    rowsMatrix X = rowsMatrix Y := by
  rw [eqRows_iff.1 h]

theorem rowsMatrix_powRows (M : Array V2) (e : ℕ) :
    rowsMatrix (powRows M e) = rowsMatrix M ^ e := by
  induction e with
  | zero => rw [powRows, rowsMatrix_idRows, pow_zero]
  | succ e ih => rw [powRows, rowsMatrix_mulRows, ih, pow_succ]

end CFSG.Sporadic.J4
