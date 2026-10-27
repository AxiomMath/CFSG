module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.Walter.Ree.Bombieri

structure F3P where
  p : ℕ
  n : ℕ
deriving DecidableEq, Repr

namespace F3P

@[expose] def zero : F3P := ⟨0, 0⟩

@[expose] def one : F3P := ⟨1, 0⟩

@[expose] def X : F3P := ⟨2, 0⟩

@[expose] def add (a b : F3P) : F3P :=
  let t := (a.p ||| b.n) ^^^ (a.n ||| b.p)
  ⟨(a.n ||| b.n) ^^^ t, (a.p ||| b.p) ^^^ t⟩

@[expose] def neg (a : F3P) : F3P := ⟨a.n, a.p⟩

@[expose] def sub (a b : F3P) : F3P := add a (neg b)

@[expose] def mulX (a : F3P) : F3P := ⟨a.p <<< 1, a.n <<< 1⟩

@[expose] def red (f : F3P) (k : ℕ) (a : F3P) : F3P :=
  if a.p.testBit k then sub a f else if a.n.testBit k then add a f else a

@[expose] def smulBit (b : F3P) (i : ℕ) (a acc : F3P) : F3P :=
  if b.p.testBit i then add acc a else if b.n.testBit i then sub acc a else acc

@[expose] def mulModAux (f : F3P) (k : ℕ) (a b : F3P) : ℕ → F3P → F3P
  | 0, acc => acc
  | i + 1, acc => mulModAux f k a b i (smulBit b i a (red f k (mulX acc)))

@[expose] def bits (m : ℕ) : ℕ := if m = 0 then 0 else Nat.log2 m + 1

@[expose] def mulMod (f : F3P) (k : ℕ) (a b : F3P) : F3P :=
  mulModAux f k a b (bits (b.p ||| b.n)) zero

@[expose] def powModAux (f : F3P) (k : ℕ) (a : F3P) (e : ℕ) : ℕ → F3P → F3P
  | 0, acc => acc
  | i + 1, acc =>
    powModAux f k a e i
      (if e.testBit i then mulMod f k (mulMod f k acc acc) a else mulMod f k acc acc)

@[expose] def powMod (f : F3P) (k : ℕ) (a : F3P) (e : ℕ) : F3P :=
  powModAux f k a e (bits e) one

@[expose] def cf (a : F3P) (i : ℕ) : ZMod 3 :=
  (if a.p.testBit i then 1 else 0) - (if a.n.testBit i then 1 else 0)

def Valid (a : F3P) : Prop := a.p &&& a.n = 0

theorem valid_iff (a : F3P) : a.Valid ↔ a.p &&& a.n = 0 := Iff.rfl

noncomputable def decode (a : F3P) : Polynomial (ZMod 3) :=
  ∑ i ∈ Finset.range (a.p + a.n + 1), Polynomial.C (a.cf i) * Polynomial.X ^ i

theorem cf_eq_zero_of_le {a : F3P} {i : ℕ} (h : a.p + a.n + 1 ≤ i) : a.cf i = 0 := by
  have hp : a.p.testBit i = false :=
    Nat.testBit_lt_two_pow ((Nat.lt_two_pow_self).trans_le' (by omega) |>.trans_le
      (Nat.pow_le_pow_right (by norm_num) le_rfl))
  have hn : a.n.testBit i = false :=
    Nat.testBit_lt_two_pow ((Nat.lt_two_pow_self).trans_le' (by omega) |>.trans_le
      (Nat.pow_le_pow_right (by norm_num) le_rfl))
  simp [cf, hp, hn]

theorem coeff_decode (a : F3P) (i : ℕ) : (decode a).coeff i = a.cf i := by
  rw [decode, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro hi
    simp only [Finset.mem_range, not_lt] at hi
    simp [cf_eq_zero_of_le (by omega : a.p + a.n + 1 ≤ i)]

theorem decode_eq_of_cf {a : F3P} {g : Polynomial (ZMod 3)}
    (h : ∀ i, a.cf i = g.coeff i) : decode a = g := by
  ext i; rw [coeff_decode, h]

theorem Valid.not_both {a : F3P} (ha : a.Valid) (i : ℕ) :
    ¬ (a.p.testBit i = true ∧ a.n.testBit i = true) := by
  rintro ⟨h1, h2⟩
  have := congrArg (fun m => m.testBit i) ha
  simp [h1, h2] at this

theorem valid_of_testBit {a : F3P} (h : ∀ i, ¬ (a.p.testBit i = true ∧ a.n.testBit i = true)) :
    a.Valid := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := h i
  simp only [Nat.testBit_land, Nat.zero_testBit]
  cases hp : a.p.testBit i <;> cases hn : a.n.testBit i <;> simp_all

theorem valid_zero : zero.Valid := by simp [Valid, zero]

theorem valid_one : one.Valid := by simp [Valid, one]

theorem valid_X : X.Valid := by simp [Valid, X]

theorem valid_add {a b : F3P} (ha : a.Valid) (hb : b.Valid) : (add a b).Valid := by
  apply valid_of_testBit
  intro i
  have h1 := ha.not_both i
  have h2 := hb.not_both i
  simp only [add, Nat.testBit_xor, Nat.testBit_or]
  revert h1 h2
  generalize a.p.testBit i = x1; generalize a.n.testBit i = x2
  generalize b.p.testBit i = x3; generalize b.n.testBit i = x4
  cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> decide

theorem valid_neg {a : F3P} (ha : a.Valid) : (neg a).Valid := by
  simpa [Valid, neg, Nat.land_comm] using ha

theorem valid_sub {a b : F3P} (ha : a.Valid) (hb : b.Valid) : (sub a b).Valid :=
  valid_add ha (valid_neg hb)

theorem valid_mulX {a : F3P} (ha : a.Valid) : (mulX a).Valid := by
  apply valid_of_testBit
  intro i
  have := ha.not_both (i - 1)
  simp only [mulX, Nat.testBit_shiftLeft]
  revert this
  generalize a.p.testBit (i - 1) = x1; generalize a.n.testBit (i - 1) = x2
  generalize decide (i ≥ 1) = x3
  cases x1 <;> cases x2 <;> cases x3 <;> decide

theorem valid_red {f a : F3P} {k : ℕ} (hf : f.Valid) (ha : a.Valid) : (red f k a).Valid := by
  unfold red
  split_ifs
  · exact valid_sub ha hf
  · exact valid_add ha hf
  · exact ha

theorem valid_smulBit {b a acc : F3P} {i : ℕ} (ha : a.Valid) (hacc : acc.Valid) :
    (smulBit b i a acc).Valid := by
  unfold smulBit
  split_ifs
  · exact valid_add hacc ha
  · exact valid_sub hacc ha
  · exact hacc

theorem valid_mulModAux {f a b : F3P} {k : ℕ} (hf : f.Valid) (ha : a.Valid) :
    ∀ (i : ℕ) {acc : F3P}, acc.Valid → (mulModAux f k a b i acc).Valid
  | 0, _, h => h
  | i + 1, _, h => valid_mulModAux hf ha i (valid_smulBit ha (valid_red hf (valid_mulX h)))

theorem valid_mulMod {f a b : F3P} {k : ℕ} (hf : f.Valid) (ha : a.Valid) :
    (mulMod f k a b).Valid :=
  valid_mulModAux hf ha _ valid_zero

theorem valid_powModAux {f a : F3P} {k e : ℕ} (hf : f.Valid) (ha : a.Valid) :
    ∀ (i : ℕ) {acc : F3P}, acc.Valid → (powModAux f k a e i acc).Valid
  | 0, _, h => h
  | i + 1, _, h => by
    simp only [powModAux]
    apply valid_powModAux hf ha i
    split_ifs
    · exact valid_mulMod hf (valid_mulMod hf h)
    · exact valid_mulMod hf h

theorem valid_powMod {f a : F3P} {k e : ℕ} (hf : f.Valid) (ha : a.Valid) :
    (powMod f k a e).Valid :=
  valid_powModAux hf ha _ valid_one

theorem cf_add {a b : F3P} (ha : a.Valid) (hb : b.Valid) (i : ℕ) :
    (add a b).cf i = a.cf i + b.cf i := by
  have h1 := ha.not_both i
  have h2 := hb.not_both i
  simp only [cf, add, Nat.testBit_xor, Nat.testBit_or]
  revert h1 h2
  generalize a.p.testBit i = x1; generalize a.n.testBit i = x2
  generalize b.p.testBit i = x3; generalize b.n.testBit i = x4
  cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> decide

theorem cf_neg (a : F3P) (i : ℕ) : (neg a).cf i = -a.cf i := by
  unfold cf neg
  exact (neg_sub _ _).symm

theorem cf_mulX (a : F3P) (i : ℕ) : (mulX a).cf i = if i = 0 then 0 else a.cf (i - 1) := by
  simp only [cf, mulX, Nat.testBit_shiftLeft]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · simp [Nat.pos_iff_ne_zero.mp hi, show 1 ≤ i from hi]

theorem decode_add {a b : F3P} (ha : a.Valid) (hb : b.Valid) :
    decode (add a b) = decode a + decode b :=
  decode_eq_of_cf fun i => by rw [cf_add ha hb, Polynomial.coeff_add, coeff_decode, coeff_decode]

theorem decode_neg (a : F3P) : decode (neg a) = -decode a :=
  decode_eq_of_cf fun i => by rw [cf_neg, Polynomial.coeff_neg, coeff_decode]

theorem decode_sub {a b : F3P} (ha : a.Valid) (hb : b.Valid) :
    decode (sub a b) = decode a - decode b := by
  rw [sub, decode_add ha (valid_neg hb), decode_neg, sub_eq_add_neg]

theorem decode_mulX (a : F3P) : decode (mulX a) = Polynomial.X * decode a :=
  decode_eq_of_cf fun i => by
    rw [cf_mulX]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [Polynomial.coeff_X_mul, coeff_decode]
      simp

theorem decode_zero : decode zero = 0 :=
  decode_eq_of_cf fun i => by simp [cf, zero]

theorem decode_one : decode one = 1 :=
  decode_eq_of_cf fun i => by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [cf, one]
    · simp [cf, one, Polynomial.coeff_one, Nat.pos_iff_ne_zero.mp hi,
        Nat.testBit_lt_two_pow (show 1 < 2 ^ i from Nat.one_lt_two_pow hi.ne')]

theorem decode_X : decode X = Polynomial.X :=
  decode_eq_of_cf fun i => by
    rw [Polynomial.coeff_X]
    rcases Nat.lt_trichotomy i 1 with h | rfl | h
    · obtain rfl : i = 0 := by omega
      simp [cf, X]
    · simp only [cf, X]; decide
    · have : (2 : ℕ).testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) h))
      simp only [cf, X, this, Nat.zero_testBit]
      simp [show ¬ (1 = i) by omega]

variable {R : Type*} [CommRing R] (ι : ZMod 3 →+* R) (r : R)

noncomputable def ev (a : F3P) : R := (decode a).eval₂ ι r

theorem ev_def (a : F3P) : ev ι r a = (decode a).eval₂ ι r := by rw [ev]

variable {ι r}

theorem ev_add {a b : F3P} (ha : a.Valid) (hb : b.Valid) :
    ev ι r (add a b) = ev ι r a + ev ι r b := by
  simp [ev, decode_add ha hb, Polynomial.eval₂_add]

theorem ev_neg (a : F3P) : ev ι r (neg a) = -ev ι r a := by
  simp [ev, decode_neg, Polynomial.eval₂_neg]

theorem ev_sub {a b : F3P} (ha : a.Valid) (hb : b.Valid) :
    ev ι r (sub a b) = ev ι r a - ev ι r b := by
  simp [ev, decode_sub ha hb, Polynomial.eval₂_sub]

theorem ev_mulX (a : F3P) : ev ι r (mulX a) = r * ev ι r a := by
  simp [ev, decode_mulX]

theorem ev_zero : ev ι r zero = 0 := by simp [ev, decode_zero]

theorem ev_one : ev ι r one = 1 := by simp [ev, decode_one]

theorem ev_X : ev ι r X = r := by simp [ev, decode_X]

theorem ev_red {f a : F3P} {k : ℕ} (hf : f.Valid) (ha : a.Valid) (hf0 : ev ι r f = 0) :
    ev ι r (red f k a) = ev ι r a := by
  unfold red
  split_ifs
  · rw [ev_sub ha hf, hf0, sub_zero]
  · rw [ev_add ha hf, hf0, add_zero]
  · rfl

theorem ev_smulBit {b a acc : F3P} {i : ℕ} (hb : b.Valid) (ha : a.Valid) (hacc : acc.Valid) :
    ev ι r (smulBit b i a acc) = ev ι r acc + ι (b.cf i) * ev ι r a := by
  have hbi := hb.not_both i
  unfold smulBit
  split_ifs with h1 h2
  · have h2' : b.n.testBit i = false := by simpa [h1] using hbi
    simp [ev_add hacc ha, cf, h1, h2']
  · have h1' : b.p.testBit i = false := by simpa using h1
    simp [ev_sub hacc ha, cf, h1', h2, sub_eq_add_neg]
  · have h1' : b.p.testBit i = false := by simpa using h1
    have h2' : b.n.testBit i = false := by simpa using h2
    simp [cf, h1', h2']

theorem lt_two_pow_bits (m : ℕ) : m < 2 ^ bits m := by
  unfold bits
  split_ifs with h
  · simp [h]
  · exact Nat.lt_log2_self

theorem cf_eq_zero_of_lt {a : F3P} {N j : ℕ} (hp : a.p < 2 ^ N) (hn : a.n < 2 ^ N) (hj : N ≤ j) :
    a.cf j = 0 := by
  have h2 : 2 ^ N ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  simp [cf, Nat.testBit_lt_two_pow (hp.trans_le h2), Nat.testBit_lt_two_pow (hn.trans_le h2)]

theorem decode_eq_sum {a : F3P} {N : ℕ} (hp : a.p < 2 ^ N) (hn : a.n < 2 ^ N) :
    decode a = ∑ j ∈ Finset.range N, Polynomial.C (a.cf j) * Polynomial.X ^ j := by
  refine decode_eq_of_cf fun i => ?_
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hi : i < N
  · rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp [hi])]
    simp
  · rw [Finset.sum_eq_zero (fun j hj => by
      have : j ≠ i := by simp at hj; omega
      simp [Ne.symm this])]
    exact cf_eq_zero_of_lt hp hn (by omega)

theorem ev_eq_sum {a : F3P} {N : ℕ} (hp : a.p < 2 ^ N) (hn : a.n < 2 ^ N) :
    ev ι r a = ∑ j ∈ Finset.range N, ι (a.cf j) * r ^ j := by
  simp [ev, decode_eq_sum hp hn, Polynomial.eval₂_finsetSum]

theorem ev_mulModAux {f a b : F3P} {k : ℕ} (hf : f.Valid) (ha : a.Valid) (hb : b.Valid)
    (hf0 : ev ι r f = 0) : ∀ (i : ℕ) {acc : F3P}, acc.Valid →
    ev ι r (mulModAux f k a b i acc) =
      ev ι r acc * r ^ i + ev ι r a * ∑ j ∈ Finset.range i, ι (b.cf j) * r ^ j
  | 0, acc, _ => by simp [mulModAux]
  | i + 1, acc, h => by
    have h1 : (red f k (mulX acc)).Valid := valid_red hf (valid_mulX h)
    rw [mulModAux, ev_mulModAux hf ha hb hf0 i (valid_smulBit ha h1), ev_smulBit hb ha h1,
      ev_red hf (valid_mulX h) hf0, ev_mulX, Finset.sum_range_succ]
    ring

theorem ev_mulMod {f a b : F3P} {k : ℕ} (hf : f.Valid) (ha : a.Valid) (hb : b.Valid)
    (hf0 : ev ι r f = 0) : ev ι r (mulMod f k a b) = ev ι r a * ev ι r b := by
  have hlt := lt_two_pow_bits (b.p ||| b.n)
  rw [mulMod, ev_mulModAux hf ha hb hf0 _ valid_zero, ev_zero, zero_mul, zero_add,
    ev_eq_sum (N := bits (b.p ||| b.n)) (Nat.left_le_or.trans_lt hlt)
      (Nat.right_le_or.trans_lt hlt)]

theorem ev_powModAux {f a : F3P} {k e : ℕ} (hf : f.Valid) (ha : a.Valid)
    (hf0 : ev ι r f = 0) : ∀ (i : ℕ) {acc : F3P}, acc.Valid →
    ev ι r (powModAux f k a e i acc) = ev ι r acc ^ 2 ^ i * ev ι r a ^ (e % 2 ^ i)
  | 0, acc, _ => by simp [powModAux, Nat.mod_one]
  | i + 1, acc, h => by
    have h2 := valid_mulMod (a := acc) (b := acc) (k := k) hf h
    simp only [powModAux]
    split_ifs with hbit
    · rw [ev_powModAux hf ha hf0 i (valid_mulMod hf h2), ev_mulMod hf h2 ha hf0,
        ev_mulMod hf h h hf0, Nat.mod_pow_succ]
      have : e / 2 ^ i % 2 = 1 := by
        simpa [Nat.testBit_eq_decide_div_mod_eq] using hbit
      rw [this, pow_succ, pow_add, mul_one]
      ring
    · rw [ev_powModAux hf ha hf0 i h2, ev_mulMod hf h h hf0, Nat.mod_pow_succ]
      have : e / 2 ^ i % 2 = 0 := by
        have := Nat.mod_two_eq_zero_or_one (e / 2 ^ i)
        simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hbit
        omega
      rw [this, mul_zero, add_zero, pow_succ]
      ring

theorem ev_powMod {f a : F3P} {k e : ℕ} (hf : f.Valid) (ha : a.Valid) (hf0 : ev ι r f = 0) :
    ev ι r (powMod f k a e) = ev ι r a ^ e := by
  rw [powMod, ev_powModAux hf ha hf0 _ valid_one, ev_one, one_pow, one_mul,
    Nat.mod_eq_of_lt (lt_two_pow_bits e)]

end F3P

end CFSG.Walter.Ree.Bombieri
