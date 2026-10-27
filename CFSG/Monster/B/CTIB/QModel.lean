module

public import Certificates.Data.CFSGNative.CTIB.Arith
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Basic

public section

namespace CFSG.Monster.B.CTIB

open Native

variable {H : Type*} [Group H]

@[expose] def xpow (x : H) (b : Bool) : H := if b then x else 1

@[expose] def ordProd (e : ℕ → H) (v n : ℕ) : H :=
  ((List.range n).map fun i => if v.testBit i then e i else 1).prod

@[expose] def qOf (e : ℕ → H) (x : H) (n : ℕ) : H := xpow x (n.testBit 22) * ordProd e n 22

structure ExtraRel (e : ℕ → H) (x : H) (G : Array ℕ) : Prop where
  e_sq : ∀ i < 22, e i * e i = 1
  x_sq : x * x = 1
  x_comm : ∀ i < 22, x * e i = e i * x
  comm : ∀ i < 22, ∀ j < 22, e i * e j = e j * e i * xpow x ((G.getD j 0).testBit i)

theorem cAtN_succ (gj u j n : ℕ) :
    cAtN gj u j (n + 1) = (cAtN gj u j n ^^ (decide (j < n) && u.testBit n && gj.testBit n)) :=
  rfl

theorem corrN_succ (G : Array ℕ) (a b m : ℕ) :
    corrN G a b (m + 1) = if b.testBit m then (corrN G a b m ^^ cAt G a m) else corrN G a b m :=
  rfl

theorem autApplyN_succ (G A : Array ℕ) (n m : ℕ) :
    autApplyN G A n (m + 1) =
      if n.testBit m then qmul G (autApplyN G A n m) (A.getD m 0) else autApplyN G A n m :=
  rfl

theorem cAtN_22 (G : Array ℕ) (u j : ℕ) : cAtN (G.getD j 0) u j 22 = cAt G u j := rfl

theorem cAtN_eq_false {gj u j n : ℕ} (h : n ≤ j + 1) : cAtN gj u j n = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cAtN_succ, ih (by omega)]
    have : ¬ j < n := by omega
    simp [this]

theorem ordProd_succ (e : ℕ → H) (v n : ℕ) :
    ordProd e v (n + 1) = ordProd e v n * (if v.testBit n then e n else 1) := by
  rw [ordProd, ordProd, List.range_succ, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem ordProd_congr (e : ℕ → H) {v w n : ℕ} (h : ∀ i < n, v.testBit i = w.testBit i) :
    ordProd e v n = ordProd e w n := by
  rw [ordProd, ordProd]
  exact congrArg List.prod (List.map_congr_left fun i hi => by rw [h i (List.mem_range.1 hi)])

theorem ordProd_eq_one (e : ℕ → H) {v n : ℕ} (h : ∀ i < n, v.testBit i = false) :
    ordProd e v n = 1 := by
  induction n with
  | zero => simp [ordProd]
  | succ n ih =>
    rw [ordProd_succ, ih fun i hi => h i (by omega), h n (by omega)]
    simp

theorem ordProd_two_pow (e : ℕ → H) (i n : ℕ) : ordProd e (2 ^ i) n = if i < n then e i else 1 := by
  induction n with
  | zero => simp [ordProd]
  | succ n ih =>
    rw [ordProd_succ, ih, Nat.testBit_two_pow]
    rcases lt_trichotomy i n with h | rfl | h
    · have h1 : i < n + 1 := by omega
      have h2 : ¬ i = n := by omega
      simp [h, h1, h2]
    · simp
    · have h1 : ¬ i < n + 1 := by omega
      have h2 : ¬ i = n := by omega
      have h3 : ¬ i < n := by omega
      simp [h1, h2, h3]

section Xpow

variable {x : H}

theorem xpow_false : xpow x false = 1 := rfl

theorem xpow_true : xpow x true = x := rfl

theorem xpow_mul_xpow (hx : x * x = 1) (b c : Bool) : xpow x b * xpow x c = xpow x (b ^^ c) := by
  cases b <;> cases c <;> simp [xpow, hx]

end Xpow

section Bits

variable {G : Array ℕ}

theorem cAtN_xor_low (gj u w : ℕ) {j m : ℕ} (hm : m ≤ j) (n : ℕ) :
    cAtN gj (u ^^^ w % 2 ^ m) j n = cAtN gj u j n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cAtN_succ, cAtN_succ, ih]
    by_cases h : j < n
    · have : (u ^^^ w % 2 ^ m).testBit n = u.testBit n := by
        rw [Nat.testBit_xor, Nat.testBit_mod_two_pow]
        have : ¬ n < m := by omega
        simp [this]
      rw [this]
    · simp [h]

theorem testBit_qmul_low (a b : ℕ) {i : ℕ} (hi : i < 22) :
    (qmul G a b).testBit i = (a.testBit i ^^ b.testBit i) := by
  rw [qmul, Nat.testBit_or, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    Nat.testBit_xor]
  split_ifs
  · rw [Nat.testBit_two_pow]
    have : ¬ 22 = i := by omega
    simp [this]
  · simp

theorem testBit_qmul_22 (a b : ℕ) :
    (qmul G a b).testBit 22 = ((a.testBit 22 ^^ b.testBit 22) ^^ corr G a b) := by
  rw [qmul, Nat.testBit_or, Nat.testBit_mod_two_pow]
  simp only [lt_self_iff_false, decide_false, Bool.false_and, Bool.false_or]
  split_ifs with h
  · rw [Nat.testBit_two_pow_self, h]
  · rw [Nat.zero_testBit]
    simpa using h

end Bits

section Rel

variable {e : ℕ → H} {x : H} {G : Array ℕ} (hR : ExtraRel e x G)

include hR

theorem comm_ordProd (v n : ℕ) (hn : n ≤ 22) : x * ordProd e v n = ordProd e v n * x := by
  induction n with
  | zero => simp [ordProd]
  | succ n ih =>
    rw [ordProd_succ, ← mul_assoc, ih (by omega), mul_assoc, mul_assoc]
    congr 1
    split_ifs
    · exact hR.x_comm n (by omega)
    · simp

theorem comm_xpow_ordProd (b : Bool) (v n : ℕ) (hn : n ≤ 22) :
    xpow x b * ordProd e v n = ordProd e v n * xpow x b := by
  cases b
  · simp [xpow]
  · exact comm_ordProd hR v n hn

theorem comm_xpow_e (b : Bool) {i : ℕ} (hi : i < 22) : xpow x b * e i = e i * xpow x b := by
  cases b
  · simp [xpow]
  · exact hR.x_comm i hi

theorem factor_mul_e {i j : ℕ} (hi : i < 22) (hj : j < 22) (b : Bool) :
    (if b then e i else 1) * e j =
      e j * (if b then e i else 1) * xpow x (b && (G.getD j 0).testBit i) := by
  cases b
  · simp [xpow]
  · simpa using hR.comm i hi j hj

theorem ordProd_mul_e (u : ℕ) {j n : ℕ} (hj : j < n) (hn : n ≤ 22) :
    ordProd e u n * e j = xpow x (cAtN (G.getD j 0) u j n) * ordProd e (u ^^^ 2 ^ j) n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjn | rfl
    ·
      rw [ordProd_succ, mul_assoc, factor_mul_e hR (by omega) (by omega), ← mul_assoc,
        ← mul_assoc, ih hjn (by omega), cAtN_succ, ordProd_succ]
      have hbit : (u ^^^ 2 ^ j).testBit n = u.testBit n := by
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        have : ¬ j = n := by omega
        simp [this]
      rw [hbit, ← xpow_mul_xpow hR.x_sq, decide_eq_true hjn, Bool.true_and]
      have hc := comm_xpow_ordProd hR (u.testBit n && (G.getD j 0).testBit n) (u ^^^ 2 ^ j) n
        (by omega)
      have hc' : xpow x (u.testBit n && (G.getD j 0).testBit n) *
          (if u.testBit n then e n else 1) =
          (if u.testBit n then e n else 1) * xpow x (u.testBit n && (G.getD j 0).testBit n) := by
        split_ifs
        · exact comm_xpow_e hR _ (by omega)
        · simp
      calc xpow x (cAtN (G.getD j 0) u j n) * ordProd e (u ^^^ 2 ^ j) n *
            (if u.testBit n then e n else 1) *
            xpow x (u.testBit n && (G.getD j 0).testBit n)
          = xpow x (cAtN (G.getD j 0) u j n) * (ordProd e (u ^^^ 2 ^ j) n *
            ((if u.testBit n then e n else 1) *
              xpow x (u.testBit n && (G.getD j 0).testBit n))) := by simp only [mul_assoc]
        _ = xpow x (cAtN (G.getD j 0) u j n) * (ordProd e (u ^^^ 2 ^ j) n *
            (xpow x (u.testBit n && (G.getD j 0).testBit n) *
              (if u.testBit n then e n else 1))) := by rw [hc']
        _ = xpow x (cAtN (G.getD j 0) u j n) * (xpow x (u.testBit n && (G.getD j 0).testBit n) *
            ordProd e (u ^^^ 2 ^ j) n * (if u.testBit n then e n else 1)) := by
          rw [← mul_assoc (ordProd e (u ^^^ 2 ^ j) n), ← hc]
        _ = _ := by simp only [mul_assoc]
    ·
      rw [ordProd_succ, ordProd_succ, cAtN_eq_false (le_refl _), xpow_false, one_mul,
        ordProd_congr e (v := u ^^^ 2 ^ j) (w := u) fun i hi => by
          rw [Nat.testBit_xor, Nat.testBit_two_pow]
          have : ¬ j = i := by omega
          simp [this]]
      have hbit : (u ^^^ 2 ^ j).testBit j = !u.testBit j := by
        rw [Nat.testBit_xor, Nat.testBit_two_pow_self]
        cases u.testBit j <;> rfl
      rw [hbit, mul_assoc]
      congr 1
      cases u.testBit j
      · simp
      · simp [hR.e_sq j (by omega)]

theorem ordProd_mul_ordProd (v w : ℕ) {m : ℕ} (hm : m ≤ 22) :
    ordProd e v 22 * ordProd e w m = xpow x (corrN G v w m) * ordProd e (v ^^^ w % 2 ^ m) 22 := by
  induction m with
  | zero =>
    rw [show corrN G v w 0 = false from rfl, xpow_false, one_mul, pow_zero, Nat.mod_one,
      Nat.xor_zero, ordProd, ordProd, List.range_zero, List.map_nil, List.prod_nil, mul_one]
  | succ m ih =>
    rw [ordProd_succ e w m, ← mul_assoc, ih (by omega), corrN_succ]
    by_cases hb : w.testBit m
    · rw [ite_eq_left hb, ite_eq_left hb, mul_assoc, ordProd_mul_e hR _ (by omega) le_rfl,
        ← mul_assoc,
        xpow_mul_xpow hR.x_sq, cAtN_xor_low _ v w le_rfl, cAtN_22]
      congr 1
      refine ordProd_congr e fun i _ => ?_
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow,
        Nat.testBit_xor, Nat.testBit_mod_two_pow]
      rcases lt_trichotomy i m with h | rfl | h
      · have h1 : i < m + 1 := by omega
        have h2 : ¬ m = i := by omega
        simp [h, h1, h2]
      · simp [hb]
      · have h1 : ¬ i < m + 1 := by omega
        have h2 : ¬ m = i := by omega
        have h3 : ¬ i < m := by omega
        simp [h1, h2, h3]
    · rw [ite_eq_right hb, ite_eq_right hb, mul_one]
      congr 1
      refine ordProd_congr e fun i _ => ?_
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      rcases lt_trichotomy i m with h | rfl | h
      · have h1 : i < m + 1 := by omega
        simp [h, h1]
      · simp [hb]
      · have h1 : ¬ i < m + 1 := by omega
        have h3 : ¬ i < m := by omega
        simp [h1, h3]

theorem qOf_mul (a b : ℕ) : qOf e x a * qOf e x b = qOf e x (qmul G a b) := by
  have hc := comm_xpow_ordProd hR (b.testBit 22) a 22 le_rfl
  have hp := ordProd_mul_ordProd hR a b (le_refl 22)
  have hcorr : corrN G a b 22 = corr G a b := rfl
  have hq : ordProd e (a ^^^ b % 2 ^ 22) 22 = ordProd e (qmul G a b) 22 :=
    ordProd_congr e fun i hi => by
      rw [testBit_qmul_low a b hi, Nat.testBit_xor, Nat.testBit_mod_two_pow, decide_eq_true hi,
        Bool.true_and]
  calc qOf e x a * qOf e x b
      = xpow x (a.testBit 22) * (ordProd e a 22 * xpow x (b.testBit 22)) * ordProd e b 22 := by
        simp only [qOf, mul_assoc]
    _ = xpow x (a.testBit 22) * xpow x (b.testBit 22) * (ordProd e a 22 * ordProd e b 22) := by
        rw [← hc]; simp only [mul_assoc]
    _ = xpow x ((a.testBit 22 ^^ b.testBit 22) ^^ corr G a b) * ordProd e (qmul G a b) 22 := by
        rw [hp, hcorr, hq, ← mul_assoc, xpow_mul_xpow hR.x_sq, xpow_mul_xpow hR.x_sq]
    _ = qOf e x (qmul G a b) := by rw [qOf, testBit_qmul_22]

omit hR in
theorem qOf_zero : qOf e x 0 = 1 := by
  rw [qOf, Nat.zero_testBit, xpow_false, one_mul, ordProd_eq_one e fun i _ => Nat.zero_testBit i]

omit hR in
theorem qOf_two_pow_22 : qOf e x (2 ^ 22) = x := by
  rw [qOf, Nat.testBit_two_pow_self, xpow_true, ordProd_eq_one e fun i hi => by
    rw [Nat.testBit_two_pow]
    have : ¬ 22 = i := by omega
    simp [this], mul_one]

omit hR in
theorem qOf_two_pow {i : ℕ} (hi : i < 22) : qOf e x (2 ^ i) = e i := by
  rw [qOf, Nat.testBit_two_pow, ordProd_two_pow e, ite_eq_left hi]
  have h22 : ¬ i = 22 := by omega
  simp [h22, xpow]

end Rel

section Hom

variable {H' : Type*} [Group H'] {e : ℕ → H} {x : H} {e' : ℕ → H'} {x' : H'} {G : Array ℕ}

theorem autApplyN_22 (A : Array ℕ) (n : ℕ) : autApplyN G A n 22 = autApply G A n := rfl

theorem map_ordProd (φ : H →* H') (v n : ℕ) :
    φ (ordProd e v n) = ((List.range n).map fun i => if v.testBit i then φ (e i) else 1).prod := by
  rw [ordProd, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  split_ifs <;> simp

theorem map_xpow (φ : H →* H') (hφx : φ x = x') (b : Bool) : φ (xpow x b) = xpow x' b := by
  cases b
  · simp [xpow]
  · simpa [xpow] using hφx

theorem qOf_autApplyN (hR' : ExtraRel e' x' G) (A : Array ℕ) (n : ℕ) {m : ℕ} (hm : m ≤ 22) :
    qOf e' x' (autApplyN G A n m) = xpow x' (n.testBit 22) *
      ((List.range m).map fun i => if n.testBit i then qOf e' x' (A.getD i 0) else 1).prod := by
  induction m with
  | zero =>
    rw [show autApplyN G A n 0 = if n.testBit 22 then 2 ^ 22 else 0 from rfl, List.range_zero,
      List.map_nil, List.prod_nil, mul_one]
    split_ifs with h
    · rw [qOf_two_pow_22, h, xpow_true]
    · rw [qOf_zero, Bool.eq_false_iff.2 h, xpow_false]
  | succ m ih =>
    rw [autApplyN_succ, List.range_succ, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc, ← ih (by omega)]
    split_ifs
    · rw [← qOf_mul hR']
    · rw [mul_one]

theorem map_qOf (hR' : ExtraRel e' x' G) (φ : H →* H') (hφx : φ x = x') (A : Array ℕ)
    (hφe : ∀ i < 22, φ (e i) = qOf e' x' (A.getD i 0)) (n : ℕ) :
    φ (qOf e x n) = qOf e' x' (autApply G A n) := by
  rw [← autApplyN_22, qOf_autApplyN hR' A n le_rfl, qOf, map_mul, map_xpow φ hφx, map_ordProd]
  congr 1
  refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
  rw [hφe i (List.mem_range.1 hi)]

end Hom

end CFSG.Monster.B.CTIB
