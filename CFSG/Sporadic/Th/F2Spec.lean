module

public import Mathlib
public import Certificates.Data.CFSGNative.Th.Core
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Th

open CFSG.Sporadic.Th.Native Finset
open scoped Matrix

namespace Native.V4

@[expose] def toVec (a : V4) : Fin 248 → ZMod 2 := fun j => if a.testBit j.val then 1 else 0

@[expose] def toNat (a : V4) : ℕ :=
  a.w0.toNat + 2 ^ 64 * a.w1.toNat + 2 ^ 128 * a.w2.toNat + 2 ^ 192 * a.w3.toNat

theorem ext_words {a b : V4} (h0 : a.w0 = b.w0) (h1 : a.w1 = b.w1) (h2 : a.w2 = b.w2)
    (h3 : a.w3 = b.w3) : a = b := by
  cases a; cases b; simp_all

theorem testBit_eq_word (a : V4) (j : ℕ) :
    a.testBit j = (a.word (j / 64)).toNat.testBit (j % 64) := by
  unfold testBit
  generalize a.word (j / 64) = w
  have hj : (UInt64.ofNat (j % 64)).toNat % 64 = j % 64 := by
    rw [UInt64.toNat_ofNat']; omega
  rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_shiftRight,
    hj, UInt64.toNat_one, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff,
    Nat.shiftRight_eq_div_pow]

theorem word_xor (a b : V4) (k : ℕ) : (a.xor b).word k = a.word k ^^^ b.word k := by
  unfold word xor; split_ifs <;> rfl

theorem testBit_xor (a b : V4) (j : ℕ) :
    (a.xor b).testBit j = (a.testBit j ^^ b.testBit j) := by
  rw [testBit_eq_word, testBit_eq_word, testBit_eq_word, word_xor, UInt64.toNat_xor,
    Nat.testBit_xor]

theorem zero_testBit (j : ℕ) : zero.testBit j = false := by
  rw [testBit_eq_word]; unfold word zero; split_ifs <;> simp

private theorem toNat_eq_nested (a : V4) : a.toNat =
    2 ^ 64 * (2 ^ 64 * (2 ^ 64 * a.w3.toNat + a.w2.toNat) + a.w1.toNat) + a.w0.toNat := by
  unfold toNat; ring

theorem testBit_toNat (a : V4) {j : ℕ} (hj : j < 256) : a.toNat.testBit j = a.testBit j := by
  rw [toNat_eq_nested, testBit_eq_word]
  rw [Nat.testBit_two_pow_mul_add _ (UInt64.toNat_lt _)]
  split_ifs with h0
  · rw [show j / 64 = 0 by omega, show j % 64 = j by omega]; rfl
  rw [Nat.testBit_two_pow_mul_add _ (UInt64.toNat_lt _)]
  split_ifs with h1
  · rw [show j / 64 = 1 by omega, show j % 64 = j - 64 by omega]; rfl
  rw [Nat.testBit_two_pow_mul_add _ (UInt64.toNat_lt _)]
  split_ifs with h2
  · rw [show j / 64 = 2 by omega, show j % 64 = j - 64 - 64 by omega]; rfl
  · rw [show j / 64 = 3 by omega, show j % 64 = j - 64 - 64 - 64 by omega]; rfl

theorem toNat_lt (a : V4) : a.toNat < 2 ^ 256 := by
  have := UInt64.toNat_lt a.w0; have := UInt64.toNat_lt a.w1
  have := UInt64.toNat_lt a.w2; have := UInt64.toNat_lt a.w3
  unfold toNat; omega

theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  have := UInt64.toNat_lt a.w0; have := UInt64.toNat_lt a.w1
  have := UInt64.toNat_lt a.w2; have := UInt64.toNat_lt a.w3
  have := UInt64.toNat_lt b.w0; have := UInt64.toNat_lt b.w1
  have := UInt64.toNat_lt b.w2; have := UInt64.toNat_lt b.w3
  unfold toNat at h
  exact ext_words (UInt64.toNat_inj.1 (by omega)) (UInt64.toNat_inj.1 (by omega))
    (UInt64.toNat_inj.1 (by omega)) (UInt64.toNat_inj.1 (by omega))

theorem toNat_inj {a b : V4} : a.toNat = b.toNat ↔ a = b :=
  toNat_injective.eq_iff

theorem toNat_zero : zero.toNat = 0 := by
  unfold toNat zero; simp

theorem toNat_eq_zero {a : V4} : a.toNat = 0 ↔ a = zero := by
  rw [← toNat_zero, toNat_inj]

theorem wf_iff_w3 (a : V4) : a.wf = true ↔ a.w3.toNat < 2 ^ 56 := by
  unfold wf
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

theorem wf_iff_toNat_lt (a : V4) : a.wf = true ↔ a.toNat < 2 ^ 248 := by
  have := UInt64.toNat_lt a.w0; have := UInt64.toNat_lt a.w1
  have := UInt64.toNat_lt a.w2
  rw [wf_iff_w3]; unfold toNat; omega

theorem wf_iff_testBit (a : V4) :
    a.wf = true ↔ ∀ j, 248 ≤ j → j < 256 → a.testBit j = false := by
  rw [wf_iff_toNat_lt]
  constructor
  · intro h j hj hj'
    rw [← testBit_toNat a hj']
    exact Nat.testBit_lt_two_pow (h.trans_le (Nat.pow_le_pow_right (by norm_num) hj))
  · intro h
    refine Nat.lt_pow_two_of_testBit _ fun j hj => ?_
    by_cases hj' : j < 256
    · rw [testBit_toNat a hj']; exact h j hj hj'
    · exact Nat.testBit_lt_two_pow ((toNat_lt a).trans_le (Nat.pow_le_pow_right (by norm_num)
        (by omega)))

theorem zero_wf : zero.wf = true := by decide

theorem xor_wf {a b : V4} (ha : a.wf = true) (hb : b.wf = true) : (a.xor b).wf = true := by
  rw [wf_iff_testBit] at *
  intro j hj hj'
  rw [testBit_xor, ha j hj hj', hb j hj hj']; rfl

theorem toVec_apply (a : V4) (j : Fin 248) : a.toVec j = if a.testBit j.val then 1 else 0 := rfl

theorem toVec_xor (a b : V4) : (a.xor b).toVec = a.toVec + b.toVec := by
  funext j
  simp only [toVec, testBit_xor, Pi.add_apply]
  cases a.testBit j.val <;> cases b.testBit j.val <;> decide

theorem toVec_zero : zero.toVec = 0 := by
  funext j; simp [toVec, zero_testBit]

theorem testBit_eq_of_toVec_eq {a b : V4} (h : a.toVec = b.toVec) {j : ℕ} (hj : j < 248) :
    a.testBit j = b.testBit j := by
  have := congrFun h ⟨j, hj⟩
  simp only [toVec] at this
  cases ha : a.testBit j <;> cases hb : b.testBit j <;> simp_all

theorem eq_of_toVec_eq {a b : V4} (ha : a.wf = true) (hb : b.wf = true)
    (h : a.toVec = b.toVec) : a = b := by
  apply toNat_injective
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 248
  · rw [testBit_toNat a (by omega), testBit_toNat b (by omega)]
    exact testBit_eq_of_toVec_eq h hj
  · have hle : 2 ^ 248 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (((wf_iff_toNat_lt a).1 ha).trans_le hle),
      Nat.testBit_lt_two_pow (((wf_iff_toNat_lt b).1 hb).trans_le hle)]

theorem toVec_inj {a b : V4} (ha : a.wf = true) (hb : b.wf = true) :
    a.toVec = b.toVec ↔ a = b :=
  ⟨eq_of_toVec_eq ha hb, fun h => h ▸ rfl⟩

theorem ne_zero_of_toVec_ne_zero {a : V4} (h : a.toVec ≠ 0) : a ≠ zero := by
  rintro rfl; exact h toVec_zero

theorem toVec_ne_zero_of_ne_zero {a : V4} (ha : a.wf = true) (h : a ≠ zero) : a.toVec ≠ 0 := by
  rw [← toVec_zero]; exact fun h' => h (eq_of_toVec_eq ha zero_wf h')

theorem beq_iff {a b : V4} : a.beq b = true ↔ a = b := by
  constructor
  · intro h
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
    exact ext_words h.1.1.1 h.1.1.2 h.1.2 h.2
  · rintro rfl; simp [beq]

theorem isZero_iff {a : V4} : a.isZero = true ↔ a = zero := by
  constructor
  · intro h
    simp only [isZero, Bool.and_eq_true, beq_iff_eq] at h
    exact ext_words h.1.1.1 h.1.1.2 h.1.2 h.2
  · rintro rfl; decide

theorem isZero_iff_toVec {a : V4} (ha : a.wf = true) : a.isZero = true ↔ a.toVec = 0 := by
  rw [isZero_iff, ← toVec_zero, toVec_inj ha zero_wf]

theorem lt_iff {a b : V4} : a.lt b = true ↔ a.toNat < b.toNat := by
  have := UInt64.toNat_lt a.w0; have := UInt64.toNat_lt a.w1
  have := UInt64.toNat_lt a.w2; have := UInt64.toNat_lt a.w3
  have := UInt64.toNat_lt b.w0; have := UInt64.toNat_lt b.w1
  have := UInt64.toNat_lt b.w2; have := UInt64.toNat_lt b.w3
  unfold lt toNat
  simp only [bne_iff_ne, ne_eq, ← UInt64.toNat_inj, UInt64.lt_iff_toNat_lt]
  split_ifs <;> simp only [decide_eq_true_eq] <;> omega

theorem lt_eq_decide (a b : V4) : a.lt b = decide (a.toNat < b.toNat) := by
  rw [Bool.eq_iff_iff, lt_iff, decide_eq_true_iff]

theorem lt_irrefl (a : V4) : a.lt a = false := by
  rw [← Bool.not_eq_true, lt_iff]; exact Nat.lt_irrefl _

theorem lt_trans {a b c : V4} (hab : a.lt b = true) (hbc : b.lt c = true) : a.lt c = true := by
  rw [lt_iff] at *; omega

theorem lt_asymm {a b : V4} (hab : a.lt b = true) : b.lt a = false := by
  rw [← Bool.not_eq_true, lt_iff] at *; omega

theorem lt_trichotomy (a b : V4) : a.lt b = true ∨ a = b ∨ b.lt a = true := by
  rw [lt_iff, lt_iff, ← toNat_inj]; omega

theorem xor_comm (a b : V4) : a.xor b = b.xor a := by
  unfold xor; rw [UInt64.xor_comm a.w0, UInt64.xor_comm a.w1, UInt64.xor_comm a.w2,
    UInt64.xor_comm a.w3]

theorem xor_assoc (a b c : V4) : (a.xor b).xor c = a.xor (b.xor c) := by
  unfold xor; simp only [UInt64.xor_assoc]

theorem xor_self (a : V4) : a.xor a = zero := by
  unfold xor zero; simp only [UInt64.xor_self]

theorem xor_zero (a : V4) : a.xor zero = a := by
  unfold xor zero; simp only [UInt64.xor_zero]

theorem zero_xor (a : V4) : zero.xor a = a := by
  rw [xor_comm, xor_zero]

theorem xor_xor_cancel_left (a b : V4) : a.xor (a.xor b) = b := by
  rw [← xor_assoc, xor_self, zero_xor]

theorem xor_xor_cancel_right (a b : V4) : (a.xor b).xor b = a := by
  rw [xor_assoc, xor_self, xor_zero]

theorem xor_xor_cancel_left' (a b : V4) : (a.xor b).xor a = b := by
  rw [xor_comm a b, xor_xor_cancel_right]

theorem xor_xor_cancel_right' (a b : V4) : b.xor (a.xor b) = a := by
  rw [xor_comm a b, xor_xor_cancel_left]

theorem setBit_testBit (a : V4) {i j : ℕ} (hi : i < 256) (hj : j < 256) :
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
  obtain hj' | hj' | hj' | hj' : j / 64 = 0 ∨ j / 64 = 1 ∨ j / 64 = 2 ∨ j / 64 = 3 := by omega
  all_goals
    obtain hi' | hi' | hi' | hi' : i / 64 = 0 ∨ i / 64 = 1 ∨ i / 64 = 2 ∨ i / 64 = 3 := by omega
  all_goals simp (config := { decide := true }) only [hj', hi', word, key, reduceIte]
  all_goals first
    | (congr 1; simp only [decide_eq_decide]; omega)
    | (have : i ≠ j := by omega
       simp [this])

private theorem foldl_setBit_testBit (f : ℕ → Bool) {n : ℕ} (hn : n ≤ 248) {i : ℕ}
    (hi : i < 256) :
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

theorem ofFn_testBit (f : ℕ → Bool) {j : ℕ} (hj : j < 248) : (ofFn f).testBit j = f j := by
  unfold ofFn; rw [foldl_setBit_testBit f le_rfl (by omega)]; simp [hj]

theorem ofFn_wf (f : ℕ → Bool) : (ofFn f).wf = true := by
  rw [wf_iff_testBit]
  intro j hj hj'
  unfold ofFn; rw [foldl_setBit_testBit f le_rfl hj']; simp; omega

theorem toVec_ofFn (f : ℕ → Bool) (j : Fin 248) :
    (ofFn f).toVec j = if f j.val then 1 else 0 := by
  rw [toVec_apply, ofFn_testBit f j.isLt]

end Native.V4

namespace Native.Key

theorem beq_iff {a b : Key} : a.beq b = true ↔ a = b := by
  unfold beq
  rw [Bool.and_eq_true, V4.beq_iff, V4.beq_iff]
  constructor
  · rintro ⟨h1, h2⟩; cases a; cases b; simp_all
  · rintro rfl; exact ⟨rfl, rfl⟩

theorem isCanonical_iff {k : Key} : k.isCanonical = true ↔ k.u.wf = true ∧ k.v.wf = true ∧
    k.u ≠ V4.zero ∧ k.u.toNat < k.v.toNat ∧ k.v.toNat < (k.u.xor k.v).toNat := by
  unfold Key.isCanonical
  simp only [Bool.and_eq_true, Bool.not_eq_true', V4.lt_iff, and_assoc]
  rw [← Bool.not_eq_true, V4.isZero_iff]

theorem toVec_of_isCanonical {k : Key} (hk : k.isCanonical = true) :
    k.u.toVec ≠ 0 ∧ k.v.toVec ≠ 0 ∧ k.u.toVec ≠ k.v.toVec := by
  obtain ⟨hu, hv, hu0, huv, -⟩ := isCanonical_iff.1 hk
  refine ⟨V4.toVec_ne_zero_of_ne_zero hu hu0, V4.toVec_ne_zero_of_ne_zero hv ?_, ?_⟩
  · intro h; rw [h, V4.toNat_zero] at huv; omega
  · rw [Ne, V4.toVec_inj hu hv]; intro h; rw [h] at huv; omega

end Native.Key

theorem rows_getD_wf {r : Array V4} (hr : ∀ x ∈ r, x.wf = true) (i : ℕ) :
    (r[i]?.getD V4.zero).wf = true := by
  cases h : r[i]? with
  | none => exact V4.zero_wf
  | some x => exact hr x (Array.mem_of_getElem? h)

private theorem getElem?_ofFn_getD {n : ℕ} (f : Fin n → V4) (i : Fin n) :
    (Array.ofFn f)[i.val]?.getD V4.zero = f i := by
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

private theorem ofFn_wf_of_forall {n : ℕ} {f : Fin n → V4} (hf : ∀ i, (f i).wf = true) :
    ∀ x ∈ Array.ofFn f, x.wf = true := by
  intro x hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact hf i

private theorem foldl_xor_toVec (P : ℕ → Prop) [DecidablePred P] (g : ℕ → V4) (n : ℕ)
    (init : V4) :
    ((List.range n).foldl (fun acc i => if P i then acc.xor (g i) else acc) init).toVec =
      init.toVec + ∑ i ∈ range n, if P i then (g i).toVec else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sum_range_succ,
      ← add_assoc, ← ih]
    split_ifs <;> simp [V4.toVec_xor]

private theorem foldl_xor_wf (P : ℕ → Prop) [DecidablePred P] (g : ℕ → V4)
    (hg : ∀ i, (g i).wf = true) (n : ℕ) {init : V4} (hinit : init.wf = true) :
    ((List.range n).foldl (fun acc i => if P i then acc.xor (g i) else acc) init).wf = true := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split_ifs
    · exact V4.xor_wf ih (hg n)
    · exact ih

theorem frEntry_toVec (rows : Array V4) (K c : ℕ) :
    (frEntry rows K c).toVec =
      ∑ i ∈ range 8, if c.testBit i then (rows[8 * K + i]?.getD V4.zero).toVec else 0 := by
  unfold frEntry
  rw [foldl_xor_toVec, V4.toVec_zero, zero_add]
  refine sum_congr rfl fun i _ => ?_
  have h : ((c >>> i) % 2 = 1) ↔ c.testBit i = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff, Nat.shiftRight_eq_div_pow]
  exact if_congr h rfl rfl

theorem frEntry_wf {rows : Array V4} (hrows : ∀ x ∈ rows, x.wf = true) (K c : ℕ) :
    (frEntry rows K c).wf = true := by
  unfold frEntry
  exact foldl_xor_wf _ _ (fun i => rows_getD_wf hrows _) _ V4.zero_wf

theorem frTable_size (rows : Array V4) : (frTable rows).size = 31 * 256 := by
  unfold frTable; exact Array.size_ofFn

theorem frTable_getElem! (rows : Array V4) {n : ℕ} (hn : n < 31 * 256) :
    (frTable rows)[n]! = frEntry rows (n / 256) (n % 256) := by
  rw [getElem!_pos (frTable rows) n (by rw [frTable_size]; exact hn)]
  unfold frTable
  rw [Array.getElem_ofFn]

private theorem byte_toNat (w s : UInt64) :
    ((w >>> s) &&& 0xFF).toNat = w.toNat >>> (s.toNat % 64) % 256 := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, show (0xFF : UInt64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem frByte_eq (rows : Array V4) {base : ℕ} (hb : base % 256 = 0) (hlt : base < 31 * 256)
    (w s : UInt64) (acc : V4) :
    frByte (frTable rows) base w s acc =
      acc.xor (frEntry rows (base / 256) (w.toNat >>> (s.toNat % 64) % 256)) := by
  unfold frByte
  rw [byte_toNat]
  generalize w.toNat >>> (s.toNat % 64) = x
  have hx := Nat.mod_lt x (show 256 > 0 by norm_num)
  rw [frTable_getElem! rows (by omega)]
  congr 2 <;> omega

theorem frByte_toVec (rows : Array V4) {base : ℕ} (hb : base % 256 = 0) (hlt : base < 31 * 256)
    (w s : UInt64) (acc : V4) :
    (frByte (frTable rows) base w s acc).toVec = acc.toVec + ∑ i ∈ range 8,
      if w.toNat.testBit (s.toNat % 64 + i) then
        (rows[8 * (base / 256) + i]?.getD V4.zero).toVec else 0 := by
  rw [frByte_eq rows hb hlt, V4.toVec_xor, frEntry_toVec]
  refine congrArg (acc.toVec + ·) ?_
  refine sum_congr rfl fun i hi => ?_
  have h : ∀ x : ℕ, (x % 256).testBit i = (decide (i < 8) && x.testBit i) :=
    fun x => Nat.testBit_mod_two_pow x 8 i
  rw [h, Nat.testBit_shiftRight]
  simp [mem_range.1 hi]

theorem frByte_wf {rows : Array V4} (hrows : ∀ x ∈ rows, x.wf = true) {base : ℕ}
    (hb : base % 256 = 0) (hlt : base < 31 * 256) (w s : UInt64) {acc : V4}
    (hacc : acc.wf = true) : (frByte (frTable rows) base w s acc).wf = true := by
  rw [frByte_eq rows hb hlt]; exact V4.xor_wf hacc (frEntry_wf hrows _ _)

private theorem frWord_eq_foldl (t : Array V4) (base : ℕ) (w : UInt64) (acc : V4) :
    frWord t base w acc =
      (List.range 8).foldl (fun acc b => frByte t (base + 256 * b) w (UInt64.ofNat (8 * b)) acc)
        acc := by
  unfold frWord; rfl

private theorem frWord7_eq_foldl (t : Array V4) (base : ℕ) (w : UInt64) (acc : V4) :
    frWord7 t base w acc =
      (List.range 7).foldl (fun acc b => frByte t (base + 256 * b) w (UInt64.ofNat (8 * b)) acc)
        acc := by
  unfold frWord7; rfl

private theorem foldl_frByte_toVec (rows : Array V4) {base : ℕ} (hb : base % 256 = 0)
    (w : UInt64) {n : ℕ} (hn : n ≤ 8) (hlt : base + 256 * n ≤ 31 * 256) (acc : V4) :
    ((List.range n).foldl
        (fun acc b => frByte (frTable rows) (base + 256 * b) w (UInt64.ofNat (8 * b)) acc)
        acc).toVec =
      acc.toVec + ∑ b ∈ range n, ∑ i ∈ range 8, if w.toNat.testBit (8 * b + i) then
        (rows[8 * (base / 256 + b) + i]?.getD V4.zero).toVec else 0 := by
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

private theorem foldl_frByte_wf {rows : Array V4} (hrows : ∀ x ∈ rows, x.wf = true) {base : ℕ}
    (hb : base % 256 = 0) (w : UInt64) {n : ℕ} (hlt : base + 256 * n ≤ 31 * 256) {acc : V4}
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

theorem frWord_toVec (rows : Array V4) (v : V4) {W base : ℕ} {w : UInt64} (hW : W < 3)
    (hbase : base = 2048 * W) (hw : w = v.word W) (acc : V4) :
    (frWord (frTable rows) base w acc).toVec = acc.toVec + ∑ m ∈ range 64,
      if v.testBit (64 * W + m) then (rows[64 * W + m]?.getD V4.zero).toVec else 0 := by
  rw [frWord_eq_foldl, foldl_frByte_toVec rows (by omega) w (le_refl 8) (by omega),
    sum_range_mul_eq _ (show 64 = 8 * 8 by norm_num)]
  refine congrArg (acc.toVec + ·) ?_
  refine sum_congr rfl fun b hb => sum_congr rfl fun i hi => ?_
  rw [mem_range] at hb hi
  refine if_congr ?_ (by rw [show 8 * (base / 256 + b) + i = 64 * W + (8 * b + i) by omega]) rfl
  rw [V4.testBit_eq_word, show (64 * W + (8 * b + i)) / 64 = W by omega,
    show (64 * W + (8 * b + i)) % 64 = 8 * b + i by omega, hw]

theorem frWord7_toVec (rows : Array V4) (v : V4) (acc : V4) :
    (frWord7 (frTable rows) 6144 v.w3 acc).toVec = acc.toVec + ∑ m ∈ range 56,
      if v.testBit (192 + m) then (rows[192 + m]?.getD V4.zero).toVec else 0 := by
  rw [frWord7_eq_foldl, foldl_frByte_toVec rows (by omega) _ (by omega) (by omega),
    sum_range_mul_eq _ (show 56 = 8 * 7 by norm_num)]
  refine congrArg (acc.toVec + ·) ?_
  refine sum_congr rfl fun b hb => sum_congr rfl fun i hi => ?_
  rw [mem_range] at hb hi
  refine if_congr ?_ (by rw [show 8 * (6144 / 256 + b) + i = 192 + (8 * b + i) by omega]) rfl
  rw [V4.testBit_eq_word, show (192 + (8 * b + i)) / 64 = 3 by omega,
    show (192 + (8 * b + i)) % 64 = 8 * b + i by omega]
  rfl

theorem frApply_frTable_toVec_eq_sum (rows : Array V4) (v : V4) :
    (frApply (frTable rows) v).toVec =
      ∑ j ∈ range 248, if v.testBit j then (rows[j]?.getD V4.zero).toVec else 0 := by
  unfold frApply
  rw [frWord7_toVec,
    frWord_toVec rows v (W := 2) (base := 4096) (w := v.w2) (by norm_num) (by norm_num) rfl,
    frWord_toVec rows v (W := 1) (base := 2048) (w := v.w1) (by norm_num) (by norm_num) rfl,
    frWord_toVec rows v (W := 0) (base := 0) (w := v.w0) (by norm_num) (by norm_num) rfl,
    V4.toVec_zero, zero_add, show range 248 = range (192 + 56) from rfl, sum_range_add,
    show range 192 = range (128 + 64) from rfl, sum_range_add,
    show range 128 = range (64 + 64) from rfl, sum_range_add]
  simp only [Nat.reduceMul, zero_add]

theorem frApply_frTable_toVec (rows : Array V4) (v : V4) :
    (frApply (frTable rows) v).toVec =
      fun i => ∑ j : Fin 248, v.toVec j * (rows[j.val]?.getD V4.zero).toVec i := by
  rw [frApply_frTable_toVec_eq_sum]
  funext i
  rw [Finset.sum_apply, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  rw [V4.toVec_apply]
  split_ifs <;> simp

theorem frApply_frTable_wf {rows : Array V4} (hrows : ∀ x ∈ rows, x.wf = true) (v : V4) :
    (frApply (frTable rows) v).wf = true := by
  unfold frApply
  rw [frWord7_eq_foldl, frWord_eq_foldl, frWord_eq_foldl, frWord_eq_foldl]
  refine foldl_frByte_wf hrows (by norm_num) _ (by norm_num) ?_
  refine foldl_frByte_wf hrows (by norm_num) _ (by norm_num) ?_
  refine foldl_frByte_wf hrows (by norm_num) _ (by norm_num) ?_
  exact foldl_frByte_wf hrows (by norm_num) _ (by norm_num) V4.zero_wf

@[expose] def rowsMatrix (r : Array V4) : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  Matrix.of fun i j => (r[i.val]?.getD V4.zero).toVec j

theorem rowsMatrix_apply (r : Array V4) (i j : Fin 248) :
    rowsMatrix r i j = (r[i.val]?.getD V4.zero).toVec j := rfl

theorem wsChar_eq_asciiWhitespace : wsChar = CFSG.Blueprint.NativeSporadic.asciiWhitespace := by
  funext c; unfold wsChar; rfl

theorem decode_apply_eq_decodeEntries (s : String) (i j : Fin 248) :
    CFSG.Blueprint.NativeSporadic.decode 2 248 1 s i j =
      (((decodeEntries s)[i.val * 248 + j.val]?.getD 0 : ℕ) : ZMod 2) := by
  unfold decodeEntries
  rw [wsChar_eq_asciiWhitespace]
  rfl

private theorem natCast_zmod_two (n : ℕ) :
    (n : ZMod 2) = if (n % 2 == 1) = true then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem rowsOf_size (s : String) : (rowsOf s).size = 248 := by
  unfold rowsOf; exact Array.size_ofFn

theorem rowsOf_wf (s : String) : ∀ x ∈ rowsOf s, x.wf = true := by
  unfold rowsOf; exact ofFn_wf_of_forall fun _ => V4.ofFn_wf _

theorem rowsMatrix_rowsOf (s : String) :
    rowsMatrix (rowsOf s) = CFSG.Blueprint.NativeSporadic.decode 2 248 1 s := by
  ext i j
  rw [decode_apply_eq_decodeEntries, rowsMatrix_apply]
  unfold rowsOf
  rw [getElem?_ofFn_getD]
  unfold rowOfEntries
  rw [V4.toVec_ofFn, List.getElem?_toArray, natCast_zmod_two]

theorem transposeRows_size (r : Array V4) : (transposeRows r).size = 248 := by
  unfold transposeRows; exact Array.size_ofFn

theorem transposeRows_wf (r : Array V4) : ∀ x ∈ transposeRows r, x.wf = true := by
  unfold transposeRows; exact ofFn_wf_of_forall fun _ => V4.ofFn_wf _

theorem rowsMatrix_transposeRows (r : Array V4) :
    rowsMatrix (transposeRows r) = (rowsMatrix r)ᵀ := by
  ext j i
  rw [Matrix.transpose_apply, rowsMatrix_apply, rowsMatrix_apply]
  unfold transposeRows
  rw [getElem?_ofFn_getD, V4.toVec_ofFn, V4.toVec_apply]

theorem mulRows_size (X Y : Array V4) : (mulRows X Y).size = X.size := by
  unfold mulRows; exact Array.size_map

theorem mulRows_wf (X : Array V4) {Y : Array V4} (hY : ∀ y ∈ Y, y.wf = true) :
    ∀ z ∈ mulRows X Y, z.wf = true := by
  intro z hz
  unfold mulRows at hz
  obtain ⟨x, -, rfl⟩ := Array.mem_map.1 hz
  exact frApply_frTable_wf hY x

theorem rowsMatrix_mulRows (X Y : Array V4) :
    rowsMatrix (mulRows X Y) = rowsMatrix X * rowsMatrix Y := by
  ext i k
  rw [Matrix.mul_apply, rowsMatrix_apply]
  unfold mulRows
  rw [Array.getElem?_map]
  simp only [rowsMatrix_apply]
  cases X[i.val]? with
  | none => simp [V4.toVec_zero]
  | some x =>
    rw [Option.map_some, Option.getD_some, Option.getD_some, frApply_frTable_toVec]

theorem idRows_size : idRows.size = 248 := by
  unfold idRows; exact Array.size_ofFn

theorem idRows_wf : ∀ x ∈ idRows, x.wf = true := by
  unfold idRows; exact ofFn_wf_of_forall fun _ => V4.ofFn_wf _

theorem rowsMatrix_idRows : rowsMatrix idRows = 1 := by
  ext i j
  rw [rowsMatrix_apply, Matrix.one_apply]
  unfold idRows
  rw [getElem?_ofFn_getD, V4.toVec_ofFn]
  by_cases h : i = j
  · subst h; simp
  · have h' : j.val ≠ i.val := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem eqRows_iff {X Y : Array V4} : eqRows X Y = true ↔ X = Y := by
  constructor
  · intro h
    unfold eqRows at h
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨hs, h⟩ := h
    refine Array.ext hs fun i h1 h2 => ?_
    have := V4.beq_iff.1 (h i (List.mem_range.2 h1))
    rwa [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some,
      Option.getD_some] at this
  · rintro rfl
    unfold eqRows
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    exact ⟨rfl, fun i _ => V4.beq_iff.2 rfl⟩

theorem rowsMatrix_eq_of_eqRows {X Y : Array V4} (h : eqRows X Y = true) :
    rowsMatrix X = rowsMatrix Y := by
  rw [eqRows_iff.1 h]

theorem frApply_transposeRows_toVec (r : Array V4) (v : V4) :
    (frApply (frTable (transposeRows r)) v).toVec = rowsMatrix r *ᵥ v.toVec := by
  rw [frApply_frTable_toVec]
  funext i
  simp only [Matrix.mulVec, dotProduct]
  refine sum_congr rfl fun j _ => ?_
  have := congrFun (congrFun (rowsMatrix_transposeRows r) j) i
  rw [rowsMatrix_apply, Matrix.transpose_apply] at this
  rw [this, mul_comm]

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

private theorem vec_add_self (x : Fin 248 → ZMod 2) : x + x = 0 := by
  funext i; exact CharTwo.add_self_eq_zero (x i)

private theorem vec_add_add_cancel_left (x y : Fin 248 → ZMod 2) : x + (x + y) = y := by
  rw [← add_assoc, vec_add_self, zero_add]

private theorem vec_add_add_cancel_right (x y : Fin 248 → ZMod 2) : x + y + y = x := by
  rw [add_assoc, vec_add_self, add_zero]

private theorem vec_add_add_cancel_left' (x y : Fin 248 → ZMod 2) : x + y + x = y := by
  rw [add_comm x y, vec_add_add_cancel_right]

private theorem vec_add_add_cancel_right' (x y : Fin 248 → ZMod 2) : y + (x + y) = x := by
  rw [add_comm x y, vec_add_add_cancel_left]

private theorem vec_eq_of_add_eq_zero {x y : Fin 248 → ZMod 2} (h : x + y = 0) : x = y := by
  rw [← vec_add_add_cancel_right x y, h, zero_add]

private theorem vec_add_eq_zero_iff {x y : Fin 248 → ZMod 2} : x + y = 0 ↔ x = y :=
  ⟨vec_eq_of_add_eq_zero, fun h => h ▸ vec_add_self x⟩

private theorem vec_zero_eq_add_iff {x y : Fin 248 → ZMod 2} : 0 = x + y ↔ x = y := by
  rw [eq_comm, vec_add_eq_zero_iff]

@[expose] def keyPlane (k : Key) : Set (Fin 248 → ZMod 2) :=
  {0, k.u.toVec, k.v.toVec, k.u.toVec + k.v.toVec}

theorem u_mem_keyPlane (k : Key) : k.u.toVec ∈ keyPlane k := by simp [keyPlane]

theorem v_mem_keyPlane (k : Key) : k.v.toVec ∈ keyPlane k := by simp [keyPlane]

theorem canon_cases (p q : V4) :
    canon p q = ⟨p, q⟩ ∨ canon p q = ⟨q, p⟩ ∨ canon p q = ⟨p, p.xor q⟩ ∨
      canon p q = ⟨p.xor q, p⟩ ∨ canon p q = ⟨q, p.xor q⟩ ∨ canon p q = ⟨p.xor q, q⟩ := by
  unfold canon
  by_cases h1 : q.lt p = true <;> by_cases h2 : (p.xor q).lt p = true <;>
    by_cases h3 : (p.xor q).lt q = true <;> by_cases h4 : p.lt q = true <;>
    simp [h1, h2, h3, h4]

theorem canon_wf {p q : V4} (hp : p.wf = true) (hq : q.wf = true) :
    (canon p q).u.wf = true ∧ (canon p q).v.wf = true := by
  have hs := V4.xor_wf hp hq
  rcases canon_cases p q with h | h | h | h | h | h <;> rw [h] <;> exact ⟨‹_›, ‹_›⟩

theorem keyPlane_canon (p q : V4) :
    keyPlane (canon p q) = {0, p.toVec, q.toVec, p.toVec + q.toVec} := by
  rcases canon_cases p q with h | h | h | h | h | h <;> rw [h] <;> ext x <;>
    simp only [keyPlane, Set.mem_insert_iff, Set.mem_singleton_iff, V4.toVec_xor,
      vec_add_add_cancel_left, vec_add_add_cancel_right, vec_add_add_cancel_left',
      vec_add_add_cancel_right', add_comm q.toVec p.toVec] <;> tauto

theorem canon_isCanonical {p q : V4} (hp : p.wf = true) (hq : q.wf = true) (hp0 : p.toVec ≠ 0)
    (hq0 : q.toVec ≠ 0) (hpq : p.toVec ≠ q.toVec) : (canon p q).isCanonical = true := by
  have hs := V4.xor_wf hp hq
  have np : p.toNat ≠ 0 := fun h => V4.ne_zero_of_toVec_ne_zero hp0 (V4.toNat_eq_zero.1 h)
  have nq : q.toNat ≠ 0 := fun h => V4.ne_zero_of_toVec_ne_zero hq0 (V4.toNat_eq_zero.1 h)
  have ns : (p.xor q).toNat ≠ 0 := fun h => hpq (vec_eq_of_add_eq_zero (by
    rw [← V4.toVec_xor, V4.toNat_eq_zero.1 h, V4.toVec_zero]))
  have npq : p.toNat ≠ q.toNat := fun h => hpq (by rw [V4.toNat_inj.1 h])
  have nps : p.toNat ≠ (p.xor q).toNat := fun h => hq0 (by
    rw [← vec_add_add_cancel_left p.toVec q.toVec, ← V4.toVec_xor, ← V4.toNat_inj.1 h,
      vec_add_self])
  have nqs : q.toNat ≠ (p.xor q).toNat := fun h => hp0 (by
    rw [← vec_add_add_cancel_right p.toVec q.toVec, ← V4.toVec_xor, ← V4.toNat_inj.1 h,
      add_comm, vec_add_self])
  unfold canon
  by_cases h1 : q.lt p = true <;> by_cases h2 : (p.xor q).lt p = true <;>
    by_cases h3 : (p.xor q).lt q = true <;> by_cases h4 : p.lt q = true <;>
    simp only [h1, h2, h3, h4, reduceIte, Bool.false_eq_true] <;>
    rw [Key.isCanonical_iff] <;>
    simp only [V4.xor_xor_cancel_left, V4.xor_xor_cancel_right, V4.xor_xor_cancel_left',
      V4.xor_xor_cancel_right', V4.xor_comm q p, ne_eq, ← V4.toNat_eq_zero] <;>
    simp only [V4.lt_iff] at h1 h2 h3 h4 <;>
    refine ⟨‹_›, ‹_›, ?_, ?_, ?_⟩ <;> omega

theorem eq_of_mem_keyPlane {k : Key} (hk : k.isCanonical = true) {x : V4} (hx : x.wf = true)
    (h : x.toVec ∈ keyPlane k) (h0 : x ≠ V4.zero) : x = k.u ∨ x = k.v ∨ x = k.u.xor k.v := by
  obtain ⟨hu, hv, -, -, -⟩ := Key.isCanonical_iff.1 hk
  simp only [keyPlane, Set.mem_insert_iff, Set.mem_singleton_iff, ← V4.toVec_xor] at h
  rcases h with h | h | h | h
  · exact absurd (V4.eq_of_toVec_eq hx V4.zero_wf (h.trans V4.toVec_zero.symm)) h0
  · exact Or.inl (V4.eq_of_toVec_eq hx hu h)
  · exact Or.inr (Or.inl (V4.eq_of_toVec_eq hx hv h))
  · exact Or.inr (Or.inr (V4.eq_of_toVec_eq hx (V4.xor_wf hu hv) h))

theorem eq_of_keyPlane_eq {k k' : Key} (hk : k.isCanonical = true) (hk' : k'.isCanonical = true)
    (h : keyPlane k = keyPlane k') : k = k' := by
  obtain ⟨hu, hv, hu0, huv, hvs⟩ := Key.isCanonical_iff.1 hk
  obtain ⟨hu', hv', hu0', huv', hvs'⟩ := Key.isCanonical_iff.1 hk'
  have hv0 : k.v ≠ V4.zero := by intro e; rw [e, V4.toNat_zero] at huv; omega
  have hv0' : k'.v ≠ V4.zero := by intro e; rw [e, V4.toNat_zero] at huv'; omega
  have m1 := eq_of_mem_keyPlane hk hu' (h ▸ u_mem_keyPlane k') hu0'
  have m2 := eq_of_mem_keyPlane hk hv' (h ▸ v_mem_keyPlane k') hv0'
  have m3 := eq_of_mem_keyPlane hk' hu (h.symm ▸ u_mem_keyPlane k) hu0
  have m4 := eq_of_mem_keyPlane hk' hv (h.symm ▸ v_mem_keyPlane k) hv0
  replace m1 : k'.u.toNat = k.u.toNat ∨ k'.u.toNat = k.v.toNat ∨
      k'.u.toNat = (k.u.xor k.v).toNat := by rcases m1 with e | e | e <;> simp [e]
  replace m2 : k'.v.toNat = k.u.toNat ∨ k'.v.toNat = k.v.toNat ∨
      k'.v.toNat = (k.u.xor k.v).toNat := by rcases m2 with e | e | e <;> simp [e]
  replace m3 : k.u.toNat = k'.u.toNat ∨ k.u.toNat = k'.v.toNat ∨
      k.u.toNat = (k'.u.xor k'.v).toNat := by rcases m3 with e | e | e <;> simp [e]
  replace m4 : k.v.toNat = k'.u.toNat ∨ k.v.toNat = k'.v.toNat ∨
      k.v.toNat = (k'.u.xor k'.v).toNat := by rcases m4 with e | e | e <;> simp [e]
  have e1 : k.u = k'.u := V4.toNat_injective (by omega)
  have e2 : k.v = k'.v := V4.toNat_injective (by omega)
  cases k; cases k'
  simp only at e1 e2
  rw [e1, e2]

theorem keyPlane_eq_span (k : Key) :
    keyPlane k = (Submodule.span (ZMod 2) {k.u.toVec, k.v.toVec} : Set (Fin 248 → ZMod 2)) := by
  ext x
  simp only [keyPlane, Set.mem_insert_iff, Set.mem_singleton_iff, SetLike.mem_coe,
    Submodule.mem_span_pair]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩
  · rintro ⟨a, b, rfl⟩
    rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;> simp

theorem linearIndependent_of_isCanonical {k : Key} (hk : k.isCanonical = true) :
    LinearIndependent (ZMod 2) ![k.u.toVec, k.v.toVec] := by
  obtain ⟨h1, h2, h3⟩ := Key.toVec_of_isCanonical hk
  have h1' := Ne.symm h1
  have h2' := Ne.symm h2
  have h3' := Ne.symm h3
  rw [LinearIndependent.pair_iffₛ]
  intro s t s' t' hst
  rcases zmod_two_cases s with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl <;>
    rcases zmod_two_cases s' with rfl | rfl <;> rcases zmod_two_cases t' with rfl | rfl <;>
    simp [vec_add_eq_zero_iff, vec_zero_eq_add_iff, h1, h2, h3, h1', h2', h3'] at hst ⊢

theorem keyPlane_imageKey (r : Array V4) (k : Key) :
    keyPlane (imageKey (frTable (transposeRows r)) k) =
      (fun v => rowsMatrix r *ᵥ v) '' keyPlane k := by
  unfold imageKey
  rw [keyPlane_canon, frApply_transposeRows_toVec, frApply_transposeRows_toVec]
  simp only [keyPlane, Set.image_insert_eq, Set.image_singleton, Matrix.mulVec_zero,
    Matrix.mulVec_add]

theorem imageKey_isCanonical (r : Array V4) {k : Key} (hk : k.isCanonical = true)
    (hr : Function.Injective fun v => rowsMatrix r *ᵥ v) :
    (imageKey (frTable (transposeRows r)) k).isCanonical = true := by
  obtain ⟨h1, h2, h3⟩ := Key.toVec_of_isCanonical hk
  unfold imageKey
  refine canon_isCanonical (frApply_frTable_wf (transposeRows_wf r) _)
    (frApply_frTable_wf (transposeRows_wf r) _) ?_ ?_ ?_ <;>
    simp only [frApply_transposeRows_toVec, ne_eq]
  · exact fun h => h1 (hr (h.trans (Matrix.mulVec_zero _).symm))
  · exact fun h => h2 (hr (h.trans (Matrix.mulVec_zero _).symm))
  · exact fun h => h3 (hr h)

end CFSG.Sporadic.Th
