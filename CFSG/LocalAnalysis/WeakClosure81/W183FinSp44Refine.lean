module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Pack
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.GH74.KGroups
open CFSG.ComponentClassification.UnbalancedCatalog

@[expose] def decodeM (M : Nat) : Matrix (Fin 4) (Fin 4) GF4 :=
  Matrix.of fun i j => GF4.ofNat' (e2 M i.val j.val)

@[expose] def encodeM (M : Matrix (Fin 4) (Fin 4) GF4) : Nat :=
  (List.finRange 4).foldl (fun acc i => (List.finRange 4).foldl (fun acc j =>
    acc ||| ((M i j).toNat <<< (2 * (4 * i.val + j.val)))) acc) 0
private theorem w183finSp44_or_bytes_eq (b0 b1 b2 b3 : Nat) (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (h3 : b3 < 256) :
    b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
      = b0 + b1 * 256 + b2 * 65536 + b3 * 16777216 := by
  have e0 : b0 ||| (b1 <<< 8) = b0 + b1 * 256 := by
    rw [show b1 <<< 8 = 2 ^ 8 * b1 by rw [Nat.shiftLeft_eq]; ring]
    rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt h0 b1]
    ring
  have hs1 : b0 + b1 * 256 < 2 ^ 16 := by omega
  have e1 : (b0 + b1 * 256) ||| (b2 <<< 16) = b0 + b1 * 256 + b2 * 65536 := by
    rw [show b2 <<< 16 = 2 ^ 16 * b2 by rw [Nat.shiftLeft_eq]; ring]
    rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hs1 b2]
    ring
  have hs2 : b0 + b1 * 256 + b2 * 65536 < 2 ^ 24 := by omega
  have e2 : (b0 + b1 * 256 + b2 * 65536) ||| (b3 <<< 24)
      = b0 + b1 * 256 + b2 * 65536 + b3 * 16777216 := by
    rw [show b3 <<< 24 = 2 ^ 24 * b3 by rw [Nat.shiftLeft_eq]; ring]
    rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hs2 b3]
    ring
  rw [e0, e1, e2]

private theorem w183finSp44_byte_extract (b0 b1 b2 b3 i : Nat) (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (h3 : b3 < 256) (hi : i < 4) :
    (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) / 256 ^ i % 256
      = [b0, b1, b2, b3][i]! := by
  have hN : b0 + b1 * 256 + b2 * 65536 + b3 * 16777216
      = b0 + 256 * (b1 + 256 * (b2 + 256 * b3)) := by ring
  rw [hN]
  have hZ1 : (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) / 256
      = b1 + 256 * (b2 + 256 * b3) := by
    rw [Nat.add_mul_div_left b0 (b1 + 256 * (b2 + 256 * b3)) (by norm_num : 0 < 256),
      Nat.div_eq_of_lt h0, Nat.zero_add]
  have hZ2 : (b1 + 256 * (b2 + 256 * b3)) / 256 = b2 + 256 * b3 := by
    rw [Nat.add_mul_div_left b1 (b2 + 256 * b3) (by norm_num : 0 < 256),
      Nat.div_eq_of_lt h1, Nat.zero_add]
  have hZ3 : (b2 + 256 * b3) / 256 = b3 := by
    rw [Nat.add_mul_div_left b2 b3 (by norm_num : 0 < 256),
      Nat.div_eq_of_lt h2, Nat.zero_add]
  interval_cases i
  · show (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) / 1 % 256 = b0
    rw [Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  · show (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) / 256 % 256 = b1
    rw [hZ1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  · show (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) / 65536 % 256 = b2
    rw [show (65536 : Nat) = 256 * 256 by norm_num, ← Nat.div_div_eq_div_mul, hZ1, hZ2,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
  · show (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) / 16777216 % 256 = b3
    rw [show (16777216 : Nat) = 256 * 256 * 256 by norm_num, ← Nat.div_div_eq_div_mul,
      ← Nat.div_div_eq_div_mul, hZ1, hZ2, hZ3, Nat.mod_eq_of_lt h3]

private theorem w183finSp44_ent_xor (x y j : Nat) : ent (x ^^^ y) j = ent x j ^^^ ent y j := by
  simp only [ent]
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]

private theorem w183finSp44_ent_row (A i k : Nat) (hk : k < 4) : ent (row A i) k = e2 A i k := by
  simp only [ent, row, e2]
  rw [Nat.shiftRight_and_distrib, ← Nat.shiftRight_add]
  have h : 255 >>> (2 * k) &&& 3 = 3 := by interval_cases k <;> decide
  rw [Nat.and_assoc, h]
  rw [show 8 * i + 2 * k = 2 * (4 * i + k) by ring]

private theorem w183finSp44_ent_scal (a b j : Nat) (ha : a < 4) (hb : b < 256) (hj : j < 4) :
    ent (scal a b) j = gmul a (ent b j) := by
  have h : ∀ a' : Fin 4, ∀ b' : Fin 256, ∀ j' : Fin 4,
      ent (scal a'.val b'.val) j'.val = gmul a'.val (ent b'.val j'.val) := by
    decide +kernel
  exact h ⟨a, ha⟩ ⟨b, hb⟩ ⟨j, hj⟩

private theorem w183finSp44_ent_lt (r k : Nat) : ent r k < 4 := by
  have h := Nat.and_lt_two_pow (r >>> (2 * k)) (show (3 : Nat) < 2 ^ 2 by norm_num)
  rw [ent]
  exact h

private theorem w183finSp44_row_lt (B k : Nat) : row B k < 256 := by
  have h := Nat.and_lt_two_pow (B >>> (8 * k)) (show (255 : Nat) < 2 ^ 8 by norm_num)
  rw [row]
  exact h

private theorem w183finSp44_scal_lt (a b : Nat) (ha : a < 4) (hb : b < 256) : scal a b < 256 := by
  have h : ∀ a' : Fin 4, ∀ b' : Fin 256, scal a'.val b'.val < 256 := by decide +kernel
  exact h ⟨a, ha⟩ ⟨b, hb⟩

private theorem w183finSp44_mulRow_lt (r B : Nat) : mulRow r B < 256 := by
  have h0 : scal (ent r 0) (row B 0) < 2 ^ 8 :=
    w183finSp44_scal_lt _ _ (w183finSp44_ent_lt r 0) (w183finSp44_row_lt B 0)
  have h1 : scal (ent r 1) (row B 1) < 2 ^ 8 :=
    w183finSp44_scal_lt _ _ (w183finSp44_ent_lt r 1) (w183finSp44_row_lt B 1)
  have h2 : scal (ent r 2) (row B 2) < 2 ^ 8 :=
    w183finSp44_scal_lt _ _ (w183finSp44_ent_lt r 2) (w183finSp44_row_lt B 2)
  have h3 : scal (ent r 3) (row B 3) < 2 ^ 8 :=
    w183finSp44_scal_lt _ _ (w183finSp44_ent_lt r 3) (w183finSp44_row_lt B 3)
  simp only [mulRow]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h0 h1) h2) h3

private theorem w183finSp44_byte_extract' (b0 b1 b2 b3 i : Nat) (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (h3 : b3 < 256) (hi : i < 4) :
    (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) >>> (8 * i) &&& 255
      = [b0, b1, b2, b3][i]! := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul, show (2 : Nat) ^ 8 = 256 by norm_num]
  rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    show (2 : Nat) ^ 8 = 256 by norm_num]
  exact w183finSp44_byte_extract b0 b1 b2 b3 i h0 h1 h2 h3 hi

private theorem w183finSp44_row_mmul (A B i : Nat) (hi : i < 4) :
    row (mmul A B) i = mulRow (row A i) B := by
  have hsum : mmul A B = mulRow (row A 0) B + mulRow (row A 1) B * 256
      + mulRow (row A 2) B * 65536 + mulRow (row A 3) B * 16777216 := by
    unfold mmul
    exact w183finSp44_or_bytes_eq _ _ _ _
      (w183finSp44_mulRow_lt ..) (w183finSp44_mulRow_lt ..)
      (w183finSp44_mulRow_lt ..) (w183finSp44_mulRow_lt ..)
  rw [hsum, row,
    w183finSp44_byte_extract' _ _ _ _ i (w183finSp44_mulRow_lt ..) (w183finSp44_mulRow_lt ..)
      (w183finSp44_mulRow_lt ..) (w183finSp44_mulRow_lt ..) hi]
  interval_cases i <;> rfl

private theorem w183finSp44_ent_mulRow (r B j : Nat) (hj : j < 4) :
    ent (mulRow r B) j = gmul (ent r 0) (ent (row B 0) j) ^^^ gmul (ent r 1) (ent (row B 1) j)
      ^^^ gmul (ent r 2) (ent (row B 2) j) ^^^ gmul (ent r 3) (ent (row B 3) j) := by
  simp only [mulRow]
  rw [w183finSp44_ent_xor, w183finSp44_ent_xor, w183finSp44_ent_xor]
  rw [w183finSp44_ent_scal _ _ _ (w183finSp44_ent_lt r 0) (w183finSp44_row_lt B 0) hj,
      w183finSp44_ent_scal _ _ _ (w183finSp44_ent_lt r 1) (w183finSp44_row_lt B 1) hj,
      w183finSp44_ent_scal _ _ _ (w183finSp44_ent_lt r 2) (w183finSp44_row_lt B 2) hj,
      w183finSp44_ent_scal _ _ _ (w183finSp44_ent_lt r 3) (w183finSp44_row_lt B 3) hj]

private theorem w183finSp44_e2_mmul (A B i j : Nat) (hi : i < 4) (hj : j < 4) :
    e2 (mmul A B) i j = gmul (e2 A i 0) (e2 B 0 j) ^^^ gmul (e2 A i 1) (e2 B 1 j)
      ^^^ gmul (e2 A i 2) (e2 B 2 j) ^^^ gmul (e2 A i 3) (e2 B 3 j) := by
  rw [← w183finSp44_ent_row (mmul A B) i j hj, w183finSp44_row_mmul A B i hi,
    w183finSp44_ent_mulRow (row A i) B j hj]
  rw [w183finSp44_ent_row A i 0 (by norm_num), w183finSp44_ent_row A i 1 (by norm_num),
    w183finSp44_ent_row A i 2 (by norm_num), w183finSp44_ent_row A i 3 (by norm_num),
    w183finSp44_ent_row B 0 j hj, w183finSp44_ent_row B 1 j hj, w183finSp44_ent_row B 2 j hj,
    w183finSp44_ent_row B 3 j hj]

private theorem w183finSp44_e2_lt (M i j : Nat) : e2 M i j < 4 := by
  have h := Nat.and_lt_two_pow (M >>> (2 * (4 * i + j))) (show (3 : Nat) < 2 ^ 2 by norm_num)
  rw [e2]
  exact h

private theorem w183finSp44_gmul_eq_mulNat (a b : Nat) : gmul a b = GF4.mulNat a b := rfl

private theorem w183finSp44_GF4_ext {x y : GF4} (h : x.val = y.val) : x = y := by
  cases x with
  | mk xv => cases y with
    | mk yv => exact congrArg GF4.mk h

private theorem w183finSp44_ofNat'_mod (x : Nat) : GF4.ofNat' (x % 4) = GF4.ofNat' x := by
  apply w183finSp44_GF4_ext
  apply Fin.ext
  simp only [GF4.ofNat']
  exact Nat.mod_eq_of_lt (Nat.mod_lt x (by norm_num))

private theorem w183finSp44_ofNat'_add (a b : Nat) :
    GF4.ofNat' a + GF4.ofNat' b = GF4.ofNat' (a ^^^ b) := by
  show GF4.ofNat' ((GF4.ofNat' a).toNat ^^^ (GF4.ofNat' b).toNat) = GF4.ofNat' (a ^^^ b)
  rw [show (GF4.ofNat' a).toNat = a % 4 from rfl, show (GF4.ofNat' b).toNat = b % 4 from rfl,
    ← Nat.xor_mod_two_pow (n := 2), w183finSp44_ofNat'_mod]

private theorem w183finSp44_ofNat'_mul {a b : Nat} (ha : a < 4) (hb : b < 4) :
    GF4.ofNat' a * GF4.ofNat' b = GF4.ofNat' (gmul a b) := by
  have ha' : (GF4.ofNat' a).toNat = a := by
    simp [GF4.toNat, GF4.ofNat', Nat.mod_eq_of_lt ha]
  have hb' : (GF4.ofNat' b).toNat = b := by
    simp [GF4.toNat, GF4.ofNat', Nat.mod_eq_of_lt hb]
  show GF4.ofNat' (GF4.mulNat (GF4.ofNat' a).toNat (GF4.ofNat' b).toNat)
      = GF4.ofNat' (gmul a b)
  rw [ha', hb', w183finSp44_gmul_eq_mulNat]

private theorem w183finSp44_sum4 (x0 x1 x2 x3 : Nat) :
    GF4.ofNat' x0 + GF4.ofNat' x1 + GF4.ofNat' x2 + GF4.ofNat' x3
      = GF4.ofNat' (x0 ^^^ x1 ^^^ x2 ^^^ x3) := by
  rw [w183finSp44_ofNat'_add, w183finSp44_ofNat'_add, w183finSp44_ofNat'_add]

theorem decodeM_mmul (A B : Nat) : decodeM (mmul A B) = decodeM A * decodeM B := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  show GF4.ofNat' (e2 (mmul A B) i.val j.val)
      = GF4.ofNat' (e2 A i.val 0) * GF4.ofNat' (e2 B 0 j.val)
        + GF4.ofNat' (e2 A i.val 1) * GF4.ofNat' (e2 B 1 j.val)
        + GF4.ofNat' (e2 A i.val 2) * GF4.ofNat' (e2 B 2 j.val)
        + GF4.ofNat' (e2 A i.val 3) * GF4.ofNat' (e2 B 3 j.val)
  rw [w183finSp44_e2_mmul A B i.val j.val i.isLt j.isLt,
    w183finSp44_ofNat'_mul (w183finSp44_e2_lt A i.val 0) (w183finSp44_e2_lt B 0 j.val),
    w183finSp44_ofNat'_mul (w183finSp44_e2_lt A i.val 1) (w183finSp44_e2_lt B 1 j.val),
    w183finSp44_ofNat'_mul (w183finSp44_e2_lt A i.val 2) (w183finSp44_e2_lt B 2 j.val),
    w183finSp44_ofNat'_mul (w183finSp44_e2_lt A i.val 3) (w183finSp44_e2_lt B 3 j.val),
    w183finSp44_sum4]

private theorem w183finSp44_testBit_e2 (g i j p : Nat) (hp : p < 2) :
    (e2 g i j).testBit p = g.testBit (2 * (4 * i + j) + p) := by
  rw [e2, Nat.testBit_and, Nat.testBit_shiftRight]
  have h3 : (3 : Nat).testBit p = true := by interval_cases p <;> decide
  rw [h3, Bool.and_true]

private theorem w183finSp44_testBit_lt_of_lt (x q : Nat) (hx : x < 4) (hq : 2 ≤ q) :
    x.testBit q = false :=
  Nat.testBit_lt_two_pow
    (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num : 0 < 2) hq))

private theorem w183finSp44_gmul_lt (a b : Nat) (ha : a < 4) (hb : b < 4) : gmul a b < 4 := by
  have h : ∀ a' : Fin 4, ∀ b' : Fin 4, gmul a'.val b'.val < 4 := by decide +kernel
  exact h ⟨a, ha⟩ ⟨b, hb⟩

private theorem w183finSp44_testBit_foldl_or (l : List Nat) (g : Nat → Nat) (acc q : Nat) :
    (l.foldl (fun acc m => acc ||| (g m <<< (2 * m))) acc).testBit q =
      (acc.testBit q || l.any (fun m => (g m <<< (2 * m)).testBit q)) := by
  induction l generalizing acc with
  | nil => simp
  | cons m l ih =>
    rw [List.foldl_cons, ih, List.any_cons, Nat.testBit_or]
    simp only [Bool.or_assoc]

private def w183finSp44_packRange (f : Nat → Nat) : Nat :=
  (List.range 16).foldl (fun acc m => acc ||| (f m <<< (2 * m))) 0

private theorem w183finSp44_testBit_packRange (f : Nat → Nat) (q : Nat) :
    (w183finSp44_packRange f).testBit q =
      (List.range 16).any (fun m => (f m <<< (2 * m)).testBit q) := by
  unfold w183finSp44_packRange
  rw [w183finSp44_testBit_foldl_or]
  simp

private theorem w183finSp44_any_range_eq (n m : Nat) (G : Nat → Bool) (hm : m < n)
    (hfalse : ∀ m' < n, m' ≠ m → G m' = false) : (List.range n).any G = G m := by
  cases h : G m
  · apply List.any_eq_false.mpr
    intro m' hm'
    rw [List.mem_range] at hm'
    by_cases h' : m' = m
    · subst h'
      rw [h]
      decide
    · rw [hfalse m' hm' h']
      decide
  · apply List.any_eq_true.mpr
    exact ⟨m, List.mem_range.mpr hm, h⟩

private theorem w183finSp44_any_range_fields (f : Nat → Nat) (m r : Nat) (hm : m < 16)
    (hr : r < 2) (hf : ∀ m' < 16, f m' < 4) :
    (List.range 16).any
        (fun m' => decide (2 * m + r ≥ 2 * m') && (f m').testBit (2 * m + r - 2 * m'))
      = (f m).testBit r := by
  have hGm : (decide (2 * m + r ≥ 2 * m) && (f m).testBit (2 * m + r - 2 * m))
      = (f m).testBit r := by
    rw [show 2 * m + r - 2 * m = r by omega,
      decide_eq_true_iff.mpr (Nat.le_add_right (2 * m) r), Bool.true_and]
  rw [← hGm]
  refine w183finSp44_any_range_eq 16 m
    (fun m' => decide (2 * m + r ≥ 2 * m') && (f m').testBit (2 * m + r - 2 * m')) hm ?_
  intro m' hm' hne
  by_cases hle : 2 * m' ≤ 2 * m + r
  · rw [decide_eq_true_iff.mpr hle, Bool.true_and]
    exact w183finSp44_testBit_lt_of_lt (f m') (2 * m + r - 2 * m') (hf m' hm') (by omega)
  · rw [decide_eq_false_iff_not.mpr (by omega), Bool.false_and]

private theorem w183finSp44_e2_packRange (f : Nat → Nat) (hf : ∀ m < 16, f m < 4)
    (A B : Nat) (hA : A < 4) (hB : B < 4) :
    e2 (w183finSp44_packRange f) A B = f (4 * A + B) := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 2
  · rw [w183finSp44_testBit_e2 _ _ _ _ hp, w183finSp44_testBit_packRange]
    simp only [Nat.testBit_shiftLeft]
    rw [w183finSp44_any_range_fields f (4 * A + B) p (by omega) hp hf]
  · rw [w183finSp44_testBit_lt_of_lt (e2 (w183finSp44_packRange f) A B) p
        (w183finSp44_e2_lt _ _ _) (not_lt.1 hp),
      w183finSp44_testBit_lt_of_lt (f (4 * A + B)) p (hf _ (by omega)) (not_lt.1 hp)]

private def w183finSp44_rhoF (g : Nat) (m : Nat) : Nat :=
  let A := m / 4
  let B := m % 4
  let i := (idxA A).1
  let j := (idxA A).2
  let k := (idxA B).1
  let l := (idxA B).2
  gmul (e2 g i k) (e2 g j l) ^^^ gmul (e2 g i l) (e2 g j k)

private theorem w183finSp44_rhoF_lt (g : Nat) (m : Nat) (hm : m < 16) :
    w183finSp44_rhoF g m < 4 := by
  have h1 : gmul (e2 g (idxA (m / 4)).1 (idxA (m % 4)).1)
      (e2 g (idxA (m / 4)).2 (idxA (m % 4)).2) < 2 ^ 2 :=
    w183finSp44_gmul_lt _ _ (w183finSp44_e2_lt ..) (w183finSp44_e2_lt ..)
  have h2 : gmul (e2 g (idxA (m / 4)).1 (idxA (m % 4)).2)
      (e2 g (idxA (m / 4)).2 (idxA (m % 4)).1) < 2 ^ 2 :=
    w183finSp44_gmul_lt _ _ (w183finSp44_e2_lt ..) (w183finSp44_e2_lt ..)
  unfold w183finSp44_rhoF
  exact Nat.xor_lt_two_pow h1 h2

private theorem w183finSp44_packRange_rho (g : Nat) :
    rho g = w183finSp44_packRange (w183finSp44_rhoF g) := by
  have h16 : List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by
    decide
  rw [w183finSp44_packRange, h16]
  simp only [List.foldl_cons, List.foldl_nil, Nat.zero_or]
  unfold rho w183finSp44_rhoF
  norm_num

private theorem w183finSp44_e2_rho (g A B : Nat) (hA : A < 4) (hB : B < 4) :
    e2 (rho g) A B = w183finSp44_rhoF g (4 * A + B) := by
  rw [w183finSp44_packRange_rho]
  exact w183finSp44_e2_packRange _ (fun m hm => w183finSp44_rhoF_lt g m hm) A B hA hB

private theorem w183finSp44_minorIdx_val (A : Fin 4) :
    idxA A.val = ((SpChain.minorIdx A).1.val, (SpChain.minorIdx A).2.val) := by
  fin_cases A <;> rfl

private def w183finSp44_rhoFG (g A B : Nat) : Nat :=
  let i := (idxA A).1
  let j := (idxA A).2
  let k := (idxA B).1
  let l := (idxA B).2
  gmul (e2 g i k) (e2 g j l) ^^^ gmul (e2 g i l) (e2 g j k)

private theorem w183finSp44_e2_rho' (g A B : Nat) (hA : A < 4) (hB : B < 4) :
    e2 (rho g) A B = w183finSp44_rhoFG g A B := by
  rw [w183finSp44_e2_rho g A B hA hB]
  unfold w183finSp44_rhoF w183finSp44_rhoFG
  rw [show (4 * A + B) / 4 = A by
        rw [Nat.add_comm (4 * A) B, Nat.add_mul_div_left B A (by norm_num),
          Nat.div_eq_of_lt hB, Nat.zero_add],
      show (4 * A + B) % 4 = B by
        rw [Nat.add_comm (4 * A) B, Nat.add_mul_mod_self_left B 4 A,
          Nat.mod_eq_of_lt hB]]

private theorem w183finSp44_GF4_sub (x y : GF4) : x - y = x + y := by
  rw [sub_eq_add_neg]
  rfl

theorem decodeM_rho (g : Nat) : decodeM (rho g) = SpChain.minorMap (decodeM g) := by
  ext A B
  rw [SpChain.minorMap_apply]
  simp only [decodeM, Matrix.of_apply]
  rw [w183finSp44_e2_rho' g A.val B.val A.isLt B.isLt]
  unfold w183finSp44_rhoFG
  rw [w183finSp44_minorIdx_val A, w183finSp44_minorIdx_val B]
  rw [w183finSp44_GF4_sub,
    w183finSp44_ofNat'_mul (w183finSp44_e2_lt g _ _) (w183finSp44_e2_lt g _ _),
    w183finSp44_ofNat'_mul (w183finSp44_e2_lt g _ _) (w183finSp44_e2_lt g _ _),
    w183finSp44_ofNat'_add]

private theorem w183finSp44_ofNat'_inj {a b : Nat} (ha : a < 4) (hb : b < 4)
    (h : GF4.ofNat' a = GF4.ofNat' b) : a = b := by
  have h1 : (GF4.ofNat' a).val.val = (GF4.ofNat' b).val.val := congrArg (fun x => x.val.val) h
  simpa [GF4.ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using h1

theorem decodeM_idM : decodeM idM = 1 := by decide +kernel

theorem decodeM_Jm : decodeM Jm = SpChain.minorJ GF4 := by decide +kernel

theorem decodeM_uMat {a b c d : Nat} (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) :
    decodeM (uMat a b c d) = SpChain.uMat (GF4.ofNat' a) (GF4.ofNat' b) (GF4.ofNat' c)
      (GF4.ofNat' d) := by
  have h : ∀ a' : Fin 4, ∀ b' : Fin 4, ∀ c' : Fin 4, ∀ d' : Fin 4,
      decodeM (uMat a'.val b'.val c'.val d'.val) =
        SpChain.uMat (GF4.ofNat' a'.val) (GF4.ofNat' b'.val) (GF4.ofNat' c'.val)
          (GF4.ofNat' d'.val) := by
    decide +kernel
  exact h ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩

theorem decodeM_inj {A B : Nat} (hA : A < 4294967296) (hB : B < 4294967296)
    (h : decodeM A = decodeM B) : A = B := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 32
  · have hi : p / 8 < 4 := by omega
    have hj : (p % 8) / 2 < 4 := by omega
    have hr : p % 2 < 2 := by omega
    have h' := congrFun (congrFun h ⟨p / 8, hi⟩) ⟨(p % 8) / 2, hj⟩
    simp only [decodeM, Matrix.of_apply] at h'
    have he : e2 A (p / 8) ((p % 8) / 2) = e2 B (p / 8) ((p % 8) / 2) :=
      w183finSp44_ofNat'_inj (w183finSp44_e2_lt A (p / 8) ((p % 8) / 2))
        (w183finSp44_e2_lt B (p / 8) ((p % 8) / 2)) h'
    have hp' : p = 2 * (4 * (p / 8) + (p % 8) / 2) + p % 2 := by omega
    rw [hp', ← w183finSp44_testBit_e2 A (p / 8) ((p % 8) / 2) (p % 2) hr,
      ← w183finSp44_testBit_e2 B (p / 8) ((p % 8) / 2) (p % 2) hr, he]
  · rw [Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.1 hp))),
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.1 hp)))]

private theorem w183finSp44_testBit_foldl_or_sh (l : List Nat) (sh g : Nat → Nat) (acc q : Nat) :
    (l.foldl (fun acc m => acc ||| (g m <<< sh m)) acc).testBit q =
      (acc.testBit q || l.any (fun m => (g m <<< sh m).testBit q)) := by
  induction l generalizing acc with
  | nil => simp
  | cons m l ih =>
    rw [List.foldl_cons, ih, List.any_cons, Nat.testBit_or]
    simp only [Bool.or_assoc]

private def w183finSp44_pack2 (sh : Nat → Nat → Nat) (f : Nat → Nat → Nat) : Nat :=
  (List.range 4).foldl (fun acc i =>
    (List.range 4).foldl (fun acc j => acc ||| (f i j <<< sh i j)) acc) 0

private theorem w183finSp44_pack2_transp (g : Nat) :
    transp g = w183finSp44_pack2 (fun i j => 2 * (4 * j + i)) (fun i j => e2 g i j) := by
  rfl

private theorem w183finSp44_testBit_pack2_aux (l : List Nat) (sh f : Nat → Nat → Nat)
    (acc q : Nat) :
    (l.foldl (fun acc i =>
        (List.range 4).foldl (fun acc j => acc ||| (f i j <<< sh i j)) acc) acc).testBit q =
      (acc.testBit q ||
        l.any (fun i => (List.range 4).any (fun j => (f i j <<< sh i j).testBit q))) := by
  induction l generalizing acc with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, ih, List.any_cons, w183finSp44_testBit_foldl_or_sh]
    simp only [Bool.or_assoc]

private theorem w183finSp44_testBit_pack2 (sh f : Nat → Nat → Nat) (q : Nat) :
    (w183finSp44_pack2 sh f).testBit q =
      (List.range 4).any (fun i => (List.range 4).any (fun j =>
        (f i j <<< sh i j).testBit q)) := by
  unfold w183finSp44_pack2
  rw [w183finSp44_testBit_pack2_aux]
  simp

private theorem w183finSp44_idx_eq {A B i j : Nat} (hA : A < 4) (hB : B < 4) (hi : i < 4)
    (hj : j < 4) (h : 4 * j + i = 4 * A + B) : i = B := by
  have h1 := congrArg (· % 4) h
  rw [Nat.add_comm (4 * j) i, Nat.add_mul_mod_self_left i 4 j, Nat.mod_eq_of_lt hi,
    Nat.add_comm (4 * A) B, Nat.add_mul_mod_self_left B 4 A, Nat.mod_eq_of_lt hB] at h1
  exact h1

private theorem w183finSp44_idx_eq2 {A B i j : Nat} (hA : A < 4) (hB : B < 4) (hi : i < 4)
    (hj : j < 4) (h : 4 * j + i = 4 * A + B) : j = A := by
  have h1 := congrArg (· / 4) h
  rw [Nat.add_comm (4 * j) i, Nat.add_mul_div_left i j (by norm_num), Nat.div_eq_of_lt hi,
    Nat.zero_add, Nat.add_comm (4 * A) B, Nat.add_mul_div_left B A (by norm_num),
    Nat.div_eq_of_lt hB, Nat.zero_add] at h1
  exact h1

private theorem w183finSp44_any_inner_transp (f : Nat → Nat → Nat) (i A B p : Nat)
    (hi : i < 4) (hA : A < 4) (hB : B < 4) (hp : p < 2) (hf : ∀ j < 4, f i j < 4) :
    (List.range 4).any (fun j => (f i j <<< (2 * (4 * j + i))).testBit (2 * (4 * A + B) + p))
      = if i = B then (f B A).testBit p else false := by
  simp only [Nat.testBit_shiftLeft]
  by_cases hib : i = B
  · subst hib
    rw [if_pos rfl]
    rw [w183finSp44_any_range_eq 4 A
      (fun j => decide (2 * (4 * A + i) + p ≥ 2 * (4 * j + i)) &&
        (f i j).testBit (2 * (4 * A + i) + p - 2 * (4 * j + i))) hA ?_]
    · rw [show (decide (2 * (4 * A + i) + p ≥ 2 * (4 * A + i)) &&
          (f i A).testBit (2 * (4 * A + i) + p - 2 * (4 * A + i))) = (f i A).testBit p by
        rw [show 2 * (4 * A + i) + p - 2 * (4 * A + i) = p by omega,
          decide_eq_true_iff.mpr (Nat.le_add_right (2 * (4 * A + i)) p), Bool.true_and]]
    · intro j hj hne
      by_cases hlt : 4 * j + i < 4 * A + i
      · rw [decide_eq_true_iff.mpr (by omega), Bool.true_and]
        exact w183finSp44_testBit_lt_of_lt (f i j) (2 * (4 * A + i) + p - 2 * (4 * j + i))
          (hf j hj) (by omega)
      · rw [decide_eq_false_iff_not.mpr (by omega), Bool.false_and]
  · rw [if_neg hib]
    apply List.any_eq_false.mpr
    intro j hj
    have hj4 : j < 4 := List.mem_range.mp hj
    by_cases hlt : 4 * j + i < 4 * A + B
    · rw [decide_eq_true_iff.mpr (by omega), Bool.true_and,
        w183finSp44_testBit_lt_of_lt (f i j) (2 * (4 * A + B) + p - 2 * (4 * j + i))
          (hf j hj4) (by omega)]
      decide
    · have hgt : 4 * A + B < 4 * j + i := by
        rcases Nat.lt_or_eq_of_le (not_lt.1 hlt) with h | h
        · exact h
        · exact absurd (w183finSp44_idx_eq hA hB hi hj4 h.symm) hib
      rw [decide_eq_false_iff_not.mpr (by omega), Bool.false_and]
      decide

private theorem w183finSp44_e2_transp (g A B : Nat) (hA : A < 4) (hB : B < 4) :
    e2 (transp g) A B = e2 g B A := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 2
  · rw [w183finSp44_testBit_e2 _ _ _ _ hp, w183finSp44_pack2_transp,
      w183finSp44_testBit_pack2]
    rw [w183finSp44_any_range_eq 4 B
      (fun i => (List.range 4).any (fun j =>
        (e2 g i j <<< (2 * (4 * j + i))).testBit (2 * (4 * A + B) + p))) hB ?_]
    · rw [w183finSp44_any_inner_transp (fun i j => e2 g i j) B A B p hB hA hB hp
        (fun j _ => w183finSp44_e2_lt g B j), if_pos rfl]
    · intro m' hm' hne
      rw [w183finSp44_any_inner_transp (fun i j => e2 g i j) m' A B p hm' hA hB hp
        (fun j _ => w183finSp44_e2_lt g m' j), if_neg hne]
  · rw [w183finSp44_testBit_lt_of_lt (e2 (transp g) A B) p
        (w183finSp44_e2_lt ..) (not_lt.1 hp),
      w183finSp44_testBit_lt_of_lt (e2 g B A) p (w183finSp44_e2_lt ..) (not_lt.1 hp)]

theorem decodeM_transp (g : Nat) : decodeM (transp g) = (decodeM g).transpose := by
  ext A B
  simp only [decodeM, Matrix.of_apply, Matrix.transpose_apply]
  rw [w183finSp44_e2_transp g A.val B.val A.isLt B.isLt]

private theorem w183finSp44_mmul_lt (A B : Nat) : mmul A B < 2 ^ 32 := by
  have h0 : mulRow (row A 0) B < 256 := w183finSp44_mulRow_lt (row A 0) B
  have h1 : mulRow (row A 1) B < 256 := w183finSp44_mulRow_lt (row A 1) B
  have h2 : mulRow (row A 2) B < 256 := w183finSp44_mulRow_lt (row A 2) B
  have h3 : mulRow (row A 3) B < 256 := w183finSp44_mulRow_lt (row A 3) B
  rw [show mmul A B = mulRow (row A 0) B + mulRow (row A 1) B * 256
      + mulRow (row A 2) B * 65536 + mulRow (row A 3) B * 16777216 by
    unfold mmul
    exact w183finSp44_or_bytes_eq _ _ _ _ h0 h1 h2 h3]
  omega

theorem symp_iff (g : Nat) : symp g = true ↔
    (decodeM g).transpose * SpChain.minorJ GF4 * decodeM g = SpChain.minorJ GF4 := by
  have hs : symp g = true ↔ mmul (mmul (transp g) Jm) g = Jm := by
    simp [symp, beq_iff_eq]
  rw [hs]
  have hmmul : decodeM (mmul (mmul (transp g) Jm) g)
      = (decodeM g).transpose * SpChain.minorJ GF4 * decodeM g := by
    rw [decodeM_mmul, decodeM_mmul, decodeM_transp, decodeM_Jm, Matrix.mul_assoc]
  constructor
  · intro h
    rw [← hmmul, h, decodeM_Jm]
  · intro h
    refine decodeM_inj (w183finSp44_mmul_lt _ _) (by norm_num [Jm]) ?_
    rw [hmmul, h, decodeM_Jm]

private theorem w183finSp44_toNat_lt (x : GF4) : x.toNat < 4 := x.val.isLt

private theorem w183finSp44_shiftLeft_lt (x s : Nat) (hx : x < 4) (hs : s ≤ 30) :
    x <<< s < 2 ^ 32 := by
  rw [Nat.shiftLeft_eq]
  calc x * 2 ^ s < 4 * 2 ^ s := (Nat.mul_lt_mul_right (Nat.two_pow_pos s)).mpr hx
    _ = 2 ^ (s + 2) := by rw [show (4 : Nat) = 2 ^ 2 by norm_num, ← pow_add, Nat.add_comm]
    _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)

private theorem w183finSp44_foldl_lt {α : Type} (l : List α) (f : Nat → α → Nat) (N : Nat)
    (hstep : ∀ a ∈ l, ∀ acc, acc < N → f acc a < N) :
    ∀ acc, acc < N → (l.foldl f acc) < N := by
  induction l with
  | nil => intro acc hacc; simpa using hacc
  | cons a l ih =>
    intro acc hacc
    rw [List.foldl_cons]
    exact ih (fun a' ha' acc' h' => hstep a' (List.mem_cons_of_mem _ ha') acc' h')
      (f acc a) (hstep a (List.mem_cons_self ..) acc hacc)

private theorem w183finSp44_foldl_or_lt {α : Type} (l : List α) (sh : α → Nat) (g : α → Nat)
    (hg : ∀ m ∈ l, g m <<< sh m < 2 ^ 32) :
    ∀ acc, acc < 2 ^ 32 → (l.foldl (fun acc m => acc ||| (g m <<< sh m)) acc) < 2 ^ 32 := by
  induction l with
  | nil => intro acc hacc; simpa using hacc
  | cons m l ih =>
    intro acc hacc
    rw [List.foldl_cons]
    exact ih (fun m' hm' => hg m' (List.mem_cons_of_mem _ hm'))
      (acc ||| (g m <<< sh m)) (Nat.or_lt_two_pow hacc (hg m (List.mem_cons_self ..)))

theorem encodeM_lt (M : Matrix (Fin 4) (Fin 4) GF4) : encodeM M < 4294967296 := by
  unfold encodeM
  refine w183finSp44_foldl_lt (List.finRange 4) _ (2 ^ 32) ?_ 0 (Nat.two_pow_pos 32)
  intro i _ acc hacc
  refine w183finSp44_foldl_or_lt (List.finRange 4) (fun j => 2 * (4 * i.val + j.val))
    (fun j => (M i j).toNat) ?_ acc hacc
  intro j _
  exact w183finSp44_shiftLeft_lt (M i j).toNat _ (w183finSp44_toNat_lt _) (by omega)

private theorem w183finSp44_testBit_foldl_or_sh' {α : Type} (l : List α) (sh g : α → Nat)
    (acc q : Nat) :
    (l.foldl (fun acc m => acc ||| (g m <<< sh m)) acc).testBit q =
      (acc.testBit q || l.any (fun m => (g m <<< sh m).testBit q)) := by
  induction l generalizing acc with
  | nil => simp
  | cons m l ih =>
    rw [List.foldl_cons, ih, List.any_cons, Nat.testBit_or]
    simp only [Bool.or_assoc]

private def w183finSp44_pack2f (sh f : Fin 4 → Fin 4 → Nat) : Nat :=
  (List.finRange 4).foldl (fun acc i =>
    (List.finRange 4).foldl (fun acc j => acc ||| (f i j <<< sh i j)) acc) 0

private theorem w183finSp44_pack2f_encodeM (M : Matrix (Fin 4) (Fin 4) GF4) :
    encodeM M = w183finSp44_pack2f (fun i j => 2 * (4 * i.val + j.val))
      (fun i j => (M i j).toNat) := by
  rfl

private theorem w183finSp44_testBit_pack2f_aux (L : List (Fin 4)) (sh f : Fin 4 → Fin 4 → Nat)
    (acc q : Nat) :
    (L.foldl (fun acc i =>
        (List.finRange 4).foldl (fun acc j => acc ||| (f i j <<< sh i j)) acc) acc).testBit q =
      (acc.testBit q ||
        L.any (fun i => (List.finRange 4).any (fun j => (f i j <<< sh i j).testBit q))) := by
  induction L generalizing acc with
  | nil => simp
  | cons i L ih =>
    rw [List.foldl_cons, ih, List.any_cons, w183finSp44_testBit_foldl_or_sh']
    simp only [Bool.or_assoc]

private theorem w183finSp44_testBit_pack2f (sh f : Fin 4 → Fin 4 → Nat) (q : Nat) :
    (w183finSp44_pack2f sh f).testBit q =
      (List.finRange 4).any (fun i => (List.finRange 4).any (fun j =>
        (f i j <<< sh i j).testBit q)) := by
  unfold w183finSp44_pack2f
  rw [w183finSp44_testBit_pack2f_aux]
  simp

private theorem w183finSp44_any_finRange_eq (m : Fin 4) (G : Fin 4 → Bool)
    (hfalse : ∀ m' ≠ m, G m' = false) : (List.finRange 4).any G = G m := by
  cases h : G m
  · apply List.any_eq_false.mpr
    intro m' _
    by_cases h' : m' = m
    · subst h'; rw [h]; decide
    · rw [hfalse m' h']; decide
  · apply List.any_eq_true.mpr
    exact ⟨m, List.mem_finRange m, h⟩

private theorem w183finSp44_any_inner_encode (f : Fin 4 → Fin 4 → Nat) (i A B : Fin 4) (p : Nat)
    (hp : p < 2) (hf : ∀ j, f i j < 4) :
    (List.finRange 4).any (fun j => (f i j <<< (2 * (4 * i.val + j.val))).testBit
        (2 * (4 * A.val + B.val) + p))
      = if i = A then (f A B).testBit p else false := by
  simp only [Nat.testBit_shiftLeft]
  by_cases hiA : i = A
  · subst hiA
    rw [if_pos rfl]
    rw [w183finSp44_any_finRange_eq B
      (fun j => decide (2 * (4 * i.val + B.val) + p ≥ 2 * (4 * i.val + j.val)) &&
        (f i j).testBit (2 * (4 * i.val + B.val) + p - 2 * (4 * i.val + j.val))) ?_]
    · rw [show (decide (2 * (4 * i.val + B.val) + p ≥ 2 * (4 * i.val + B.val)) &&
          (f i B).testBit (2 * (4 * i.val + B.val) + p - 2 * (4 * i.val + B.val)))
          = (f i B).testBit p by
        rw [show 2 * (4 * i.val + B.val) + p - 2 * (4 * i.val + B.val) = p by omega,
          decide_eq_true_iff.mpr (Nat.le_add_right (2 * (4 * i.val + B.val)) p), Bool.true_and]]
    · intro j hne
      have hjB : j.val ≠ B.val := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hjB with hlt | hgt
      · rw [decide_eq_true_iff.mpr (by simp only [ge_iff_le]; omega), Bool.true_and,
          w183finSp44_testBit_lt_of_lt (f i j) _ (hf j) (by omega)]
      · rw [decide_eq_false_iff_not.mpr (by simp only [ge_iff_le, not_le]; omega), Bool.false_and]
  · rw [if_neg hiA]
    apply List.any_eq_false.mpr
    intro j _
    by_cases hlt : 4 * i.val + j.val < 4 * A.val + B.val
    · rw [decide_eq_true_iff.mpr (by simp only [ge_iff_le]; omega), Bool.true_and,
        w183finSp44_testBit_lt_of_lt (f i j) _ (hf j) (by omega)]
      decide
    · have hgt : 4 * A.val + B.val < 4 * i.val + j.val := by
        rcases Nat.lt_or_eq_of_le (not_lt.1 hlt) with h | h
        · exact h
        · exact absurd (Fin.ext (w183finSp44_idx_eq2 A.isLt B.isLt j.isLt i.isLt h.symm)) hiA
      rw [decide_eq_false_iff_not.mpr (by simp only [ge_iff_le, not_le]; omega), Bool.false_and]
      decide

private theorem w183finSp44_e2_encodeM (M : Matrix (Fin 4) (Fin 4) GF4) (A B : Fin 4) :
    e2 (encodeM M) A.val B.val = (M A B).toNat := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 2
  · rw [w183finSp44_testBit_e2 _ _ _ _ hp, w183finSp44_pack2f_encodeM,
      w183finSp44_testBit_pack2f]
    rw [w183finSp44_any_finRange_eq A
      (fun i => (List.finRange 4).any (fun j =>
        ((M i j).toNat <<< (2 * (4 * i.val + j.val))).testBit (2 * (4 * A.val + B.val) + p))) ?_]
    · rw [w183finSp44_any_inner_encode (fun i j => (M i j).toNat) A A B p hp
        (fun j => w183finSp44_toNat_lt _), if_pos rfl]
    · intro m' hne
      rw [w183finSp44_any_inner_encode (fun i j => (M i j).toNat) m' A B p hp
        (fun j => w183finSp44_toNat_lt _), if_neg hne]
  · rw [w183finSp44_testBit_lt_of_lt (e2 (encodeM M) A.val B.val) p
        (w183finSp44_e2_lt ..) (not_lt.1 hp),
      w183finSp44_testBit_lt_of_lt (M A B).toNat p (w183finSp44_toNat_lt _) (not_lt.1 hp)]

theorem decodeM_encodeM (M : Matrix (Fin 4) (Fin 4) GF4) : decodeM (encodeM M) = M := by
  ext A B
  simp only [decodeM, Matrix.of_apply]
  rw [w183finSp44_e2_encodeM M A B]
  apply w183finSp44_GF4_ext
  apply Fin.ext
  simp only [GF4.ofNat', GF4.toNat]
  exact Nat.mod_eq_of_lt (w183finSp44_toNat_lt _)

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
