module

public import CFSG.Sporadic.Fi23.WideSpec
public import Certificates.Data.CFSGNative.Fi24.Wide

public section

namespace CFSG.Sporadic.Fi24.Native

open CFSG.F3.Native

@[expose] def W.val (a : W) (j : ℕ) : ZMod 3 := bitVal (a.bitP j) (a.bitM j)

theorem W.bitP_eq (a : W) (j : ℕ) : a.bitP j = (a.limbP (j / 64)).toNat.testBit (j % 64) := by
  rw [W.bitP, CFSG.Sporadic.Fi23.Native.uint64_bit, CFSG.Sporadic.Fi23.Native.shiftRight_six]

theorem W.bitM_eq (a : W) (j : ℕ) : a.bitM j = (a.limbM (j / 64)).toNat.testBit (j % 64) := by
  rw [W.bitM, CFSG.Sporadic.Fi23.Native.uint64_bit, CFSG.Sporadic.Fi23.Native.shiftRight_six]

theorem W.limbP_ge (a : W) {l : ℕ} (hl : 13 ≤ l) : a.limbP l = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 13 := ⟨l - 13, by omega⟩
  simp [W.limbP]

theorem W.limbM_ge (a : W) {l : ℕ} (hl : 13 ≤ l) : a.limbM l = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 13 := ⟨l - 13, by omega⟩
  simp [W.limbM]

theorem W.limbP_add (a b : W) (l : ℕ) :
    (a.add b).limbP l = sumP (a.limbP l) (a.limbM l) (b.limbP l) (b.limbM l) := by
  by_cases hl : l < 13
  · interval_cases l <;> rfl
  · rw [W.limbP_ge _ (by omega), W.limbP_ge _ (by omega), W.limbM_ge _ (by omega),
      W.limbP_ge _ (by omega), W.limbM_ge _ (by omega)]
    decide

theorem W.limbM_add (a b : W) (l : ℕ) :
    (a.add b).limbM l = sumM (a.limbP l) (a.limbM l) (b.limbP l) (b.limbM l) := by
  by_cases hl : l < 13
  · interval_cases l <;> rfl
  · rw [W.limbM_ge _ (by omega), W.limbP_ge _ (by omega), W.limbM_ge _ (by omega),
      W.limbP_ge _ (by omega), W.limbM_ge _ (by omega)]
    decide

theorem W.limbP_sub (a b : W) (l : ℕ) :
    (a.sub b).limbP l = sumP (a.limbP l) (a.limbM l) (b.limbM l) (b.limbP l) := by
  by_cases hl : l < 13
  · interval_cases l <;> rfl
  · rw [W.limbP_ge _ (by omega), W.limbP_ge _ (by omega), W.limbM_ge _ (by omega),
      W.limbP_ge _ (by omega), W.limbM_ge _ (by omega)]
    decide

theorem W.limbM_sub (a b : W) (l : ℕ) :
    (a.sub b).limbM l = sumM (a.limbP l) (a.limbM l) (b.limbM l) (b.limbP l) := by
  by_cases hl : l < 13
  · interval_cases l <;> rfl
  · rw [W.limbM_ge _ (by omega), W.limbP_ge _ (by omega), W.limbM_ge _ (by omega),
      W.limbP_ge _ (by omega), W.limbM_ge _ (by omega)]
    decide

theorem W.limbP_neg (a : W) (l : ℕ) : a.neg.limbP l = a.limbM l := by
  by_cases hl : l < 13
  · interval_cases l <;> rfl
  · rw [W.limbP_ge _ (by omega), W.limbM_ge _ (by omega)]

theorem W.limbM_neg (a : W) (l : ℕ) : a.neg.limbM l = a.limbP l := by
  by_cases hl : l < 13
  · interval_cases l <;> rfl
  · rw [W.limbM_ge _ (by omega), W.limbP_ge _ (by omega)]

theorem W.limbP_zero (l : ℕ) : W.zero.limbP l = 0 := by
  by_cases hl : l < 13
  · interval_cases l <;> rfl
  · rw [W.limbP_ge _ (by omega)]

theorem W.limbM_zero (l : ℕ) : W.zero.limbM l = 0 := by
  by_cases hl : l < 13
  · interval_cases l <;> rfl
  · rw [W.limbM_ge _ (by omega)]

theorem W.ext_limbs {a b : W} (hp : ∀ l < 13, a.limbP l = b.limbP l)
    (hm : ∀ l < 13, a.limbM l = b.limbM l) : a = b := by
  have p0 : a.p0 = b.p0 := hp 0 (by norm_num)
  have p1 : a.p1 = b.p1 := hp 1 (by norm_num)
  have p2 : a.p2 = b.p2 := hp 2 (by norm_num)
  have p3 : a.p3 = b.p3 := hp 3 (by norm_num)
  have p4 : a.p4 = b.p4 := hp 4 (by norm_num)
  have p5 : a.p5 = b.p5 := hp 5 (by norm_num)
  have p6 : a.p6 = b.p6 := hp 6 (by norm_num)
  have p7 : a.p7 = b.p7 := hp 7 (by norm_num)
  have p8 : a.p8 = b.p8 := hp 8 (by norm_num)
  have p9 : a.p9 = b.p9 := hp 9 (by norm_num)
  have p10 : a.p10 = b.p10 := hp 10 (by norm_num)
  have p11 : a.p11 = b.p11 := hp 11 (by norm_num)
  have p12 : a.p12 = b.p12 := hp 12 (by norm_num)
  have m0 : a.m0 = b.m0 := hm 0 (by norm_num)
  have m1 : a.m1 = b.m1 := hm 1 (by norm_num)
  have m2 : a.m2 = b.m2 := hm 2 (by norm_num)
  have m3 : a.m3 = b.m3 := hm 3 (by norm_num)
  have m4 : a.m4 = b.m4 := hm 4 (by norm_num)
  have m5 : a.m5 = b.m5 := hm 5 (by norm_num)
  have m6 : a.m6 = b.m6 := hm 6 (by norm_num)
  have m7 : a.m7 = b.m7 := hm 7 (by norm_num)
  have m8 : a.m8 = b.m8 := hm 8 (by norm_num)
  have m9 : a.m9 = b.m9 := hm 9 (by norm_num)
  have m10 : a.m10 = b.m10 := hm 10 (by norm_num)
  have m11 : a.m11 = b.m11 := hm 11 (by norm_num)
  have m12 : a.m12 = b.m12 := hm 12 (by norm_num)
  cases a; cases b
  simp only at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12
  simp only at m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12
  subst p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12
  subst m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12
  rfl

theorem uint64_eq_of_testBit {x y : UInt64} (h : ∀ t < 64, x.toNat.testBit t = y.toNat.testBit t) :
    x = y := by
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 64
  · exact h t ht
  · rw [CFSG.Sporadic.Fi23.Native.testBit_toNat_ge _ (by omega),
      CFSG.Sporadic.Fi23.Native.testBit_toNat_ge _ (by omega)]

theorem W.wf_limb {a : W} (h : a.wf = true) (l : ℕ) : a.limbP l &&& a.limbM l = 0 := by
  unfold W.wf at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  by_cases hl : l < 13
  · interval_cases l <;> simp_all [W.limbP, W.limbM]
  · rw [W.limbP_ge _ (by omega), W.limbM_ge _ (by omega)]; rfl

theorem W.not_both {a : W} (h : a.wf = true) (j : ℕ) : (a.bitP j && a.bitM j) = false := by
  rw [W.bitP_eq, W.bitM_eq, ← Nat.testBit_and, ← UInt64.toNat_and, W.wf_limb h]
  simp

theorem W.wf_of_limbs {a : W} (h : ∀ l < 13, a.limbP l &&& a.limbM l = 0) : a.wf = true := by
  have h0 : a.p0 &&& a.m0 = 0 := h 0 (by norm_num)
  have h1 : a.p1 &&& a.m1 = 0 := h 1 (by norm_num)
  have h2 : a.p2 &&& a.m2 = 0 := h 2 (by norm_num)
  have h3 : a.p3 &&& a.m3 = 0 := h 3 (by norm_num)
  have h4 : a.p4 &&& a.m4 = 0 := h 4 (by norm_num)
  have h5 : a.p5 &&& a.m5 = 0 := h 5 (by norm_num)
  have h6 : a.p6 &&& a.m6 = 0 := h 6 (by norm_num)
  have h7 : a.p7 &&& a.m7 = 0 := h 7 (by norm_num)
  have h8 : a.p8 &&& a.m8 = 0 := h 8 (by norm_num)
  have h9 : a.p9 &&& a.m9 = 0 := h 9 (by norm_num)
  have h10 : a.p10 &&& a.m10 = 0 := h 10 (by norm_num)
  have h11 : a.p11 &&& a.m11 = 0 := h 11 (by norm_num)
  have h12 : a.p12 &&& a.m12 = 0 := h 12 (by norm_num)
  unfold W.wf
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, beq_self_eq_true, Bool.and_self]

theorem W.wf_of_bits {a : W} (h : ∀ j, (a.bitP j && a.bitM j) = false) : a.wf = true := by
  apply W.wf_of_limbs
  intro l hl
  apply uint64_eq_of_testBit
  intro t ht
  have := h (64 * l + t)
  rw [W.bitP_eq, W.bitM_eq, show (64 * l + t) / 64 = l by omega,
    show (64 * l + t) % 64 = t by omega] at this
  rw [UInt64.toNat_and, Nat.testBit_and, this]
  simp

theorem testBit_sumP (ap am bp bm : UInt64) (t : ℕ) :
    (sumP ap am bp bm).toNat.testBit t = ((am.toNat.testBit t || bm.toNat.testBit t) ^^
      ((ap.toNat.testBit t || bm.toNat.testBit t) ^^
        (am.toNat.testBit t || bp.toNat.testBit t))) := by
  simp [sumP, sumT, Nat.testBit_xor, Nat.testBit_or]

theorem testBit_sumM (ap am bp bm : UInt64) (t : ℕ) :
    (sumM ap am bp bm).toNat.testBit t = ((ap.toNat.testBit t || bp.toNat.testBit t) ^^
      ((ap.toNat.testBit t || bm.toNat.testBit t) ^^
        (am.toNat.testBit t || bp.toNat.testBit t))) := by
  simp [sumM, sumT, Nat.testBit_xor, Nat.testBit_or]

private theorem add_table : ∀ ap am bp bm : Bool, (ap && am) = false → (bp && bm) = false →
    bitVal ((am || bm) ^^ ((ap || bm) ^^ (am || bp))) ((ap || bp) ^^ ((ap || bm) ^^ (am || bp))) =
      bitVal ap am + bitVal bp bm ∧
    (((am || bm) ^^ ((ap || bm) ^^ (am || bp))) && ((ap || bp) ^^ ((ap || bm) ^^ (am || bp)))) =
      false := by
  decide

theorem W.bits_add (a b : W) (j : ℕ) :
    (a.add b).bitP j =
        ((a.bitM j || b.bitM j) ^^ ((a.bitP j || b.bitM j) ^^ (a.bitM j || b.bitP j)))
      ∧ (a.add b).bitM j =
        ((a.bitP j || b.bitP j) ^^ ((a.bitP j || b.bitM j) ^^ (a.bitM j || b.bitP j))) := by
  constructor <;>
    simp only [W.bitP_eq, W.bitM_eq, W.limbP_add, W.limbM_add, testBit_sumP, testBit_sumM]

theorem W.val_add {a b : W} (ha : a.wf = true) (hb : b.wf = true) (j : ℕ) :
    (a.add b).val j = a.val j + b.val j := by
  obtain ⟨hp, hm⟩ := W.bits_add a b j
  unfold W.val
  rw [hp, hm]
  exact (add_table _ _ _ _ (W.not_both ha j) (W.not_both hb j)).1

theorem W.wf_add {a b : W} (ha : a.wf = true) (hb : b.wf = true) : (a.add b).wf = true := by
  apply W.wf_of_bits
  intro j
  obtain ⟨hp, hm⟩ := W.bits_add a b j
  rw [hp, hm]
  exact (add_table _ _ _ _ (W.not_both ha j) (W.not_both hb j)).2

theorem W.bitP_neg (a : W) (j : ℕ) : a.neg.bitP j = a.bitM j := by
  rw [W.bitP_eq, W.bitM_eq, W.limbP_neg]

theorem W.bitM_neg (a : W) (j : ℕ) : a.neg.bitM j = a.bitP j := by
  rw [W.bitP_eq, W.bitM_eq, W.limbM_neg]

private theorem neg_table : ∀ p m : Bool, (p && m) = false → bitVal m p = -bitVal p m := by
  decide

theorem W.val_neg {a : W} (ha : a.wf = true) (j : ℕ) : a.neg.val j = -a.val j := by
  unfold W.val
  rw [W.bitP_neg, W.bitM_neg]
  exact neg_table _ _ (W.not_both ha j)

theorem W.wf_neg {a : W} (ha : a.wf = true) : a.neg.wf = true := by
  apply W.wf_of_bits
  intro j
  rw [W.bitP_neg, W.bitM_neg, Bool.and_comm]
  exact W.not_both ha j

theorem W.sub_eq_add_neg (a b : W) : a.sub b = a.add b.neg := by
  apply W.ext_limbs
  · intro l _; rw [W.limbP_sub, W.limbP_add, W.limbP_neg, W.limbM_neg]
  · intro l _; rw [W.limbM_sub, W.limbM_add, W.limbP_neg, W.limbM_neg]

theorem W.val_sub {a b : W} (ha : a.wf = true) (hb : b.wf = true) (j : ℕ) :
    (a.sub b).val j = a.val j - b.val j := by
  rw [W.sub_eq_add_neg, W.val_add ha (W.wf_neg hb), W.val_neg hb]
  exact (_root_.sub_eq_add_neg _ _).symm

theorem W.wf_sub {a b : W} (ha : a.wf = true) (hb : b.wf = true) : (a.sub b).wf = true := by
  rw [W.sub_eq_add_neg]; exact W.wf_add ha (W.wf_neg hb)

theorem W.bitP_zero (j : ℕ) : W.zero.bitP j = false := by
  rw [W.bitP_eq, W.limbP_zero]; simp

theorem W.bitM_zero (j : ℕ) : W.zero.bitM j = false := by
  rw [W.bitM_eq, W.limbM_zero]; simp

theorem W.val_zero (j : ℕ) : W.zero.val j = 0 := by
  unfold W.val; rw [W.bitP_zero, W.bitM_zero]; rfl

theorem W.wf_zero : W.zero.wf = true := by decide

theorem W.default_eq : (default : W) = W.zero := rfl

@[expose] def bitOf (j : ℕ) : UInt64 := (1 : UInt64) <<< (j &&& 63).toUInt64

theorem W.limbP_setTrit_one (a : W) {j : ℕ} (hj : j < 832) (l : ℕ) :
    (a.setTrit j 1).limbP l = if l = j / 64 then a.limbP l ||| bitOf j else a.limbP l := by
  have hq : j >>> 6 = j / 64 := CFSG.Sporadic.Fi23.Native.shiftRight_six j
  unfold W.setTrit
  simp only [hq, ↓reduceIte]
  unfold bitOf
  generalize (1 : UInt64) <<< (j &&& 63).toUInt64 = b
  have hq13 : j / 64 < 13 := by omega
  generalize j / 64 = q at hq13 ⊢
  by_cases hl : l < 13
  · interval_cases q <;> interval_cases l <;> rfl
  · rw [W.limbP_ge _ (by omega), W.limbP_ge _ (by omega), ite_eq_right (by omega)]

theorem W.limbM_setTrit_one (a : W) {j : ℕ} (hj : j < 832) (l : ℕ) :
    (a.setTrit j 1).limbM l = a.limbM l := by
  have hq : j >>> 6 = j / 64 := CFSG.Sporadic.Fi23.Native.shiftRight_six j
  unfold W.setTrit
  simp only [hq, ↓reduceIte]
  generalize (1 : UInt64) <<< (j &&& 63).toUInt64 = b
  have hq13 : j / 64 < 13 := by omega
  generalize j / 64 = q at hq13 ⊢
  by_cases hl : l < 13
  · interval_cases q <;> interval_cases l <;> rfl
  · rw [W.limbM_ge _ (by omega), W.limbM_ge _ (by omega)]

theorem W.limbP_setTrit_two (a : W) {j : ℕ} (hj : j < 832) (l : ℕ) :
    (a.setTrit j 2).limbP l = a.limbP l := by
  have hq : j >>> 6 = j / 64 := CFSG.Sporadic.Fi23.Native.shiftRight_six j
  unfold W.setTrit
  simp only [hq, ↓reduceIte]
  generalize (1 : UInt64) <<< (j &&& 63).toUInt64 = b
  have hq13 : j / 64 < 13 := by omega
  generalize j / 64 = q at hq13 ⊢
  by_cases hl : l < 13
  · interval_cases q <;> interval_cases l <;> rfl
  · rw [W.limbP_ge _ (by omega), W.limbP_ge _ (by omega)]

theorem W.limbM_setTrit_two (a : W) {j : ℕ} (hj : j < 832) (l : ℕ) :
    (a.setTrit j 2).limbM l = if l = j / 64 then a.limbM l ||| bitOf j else a.limbM l := by
  have hq : j >>> 6 = j / 64 := CFSG.Sporadic.Fi23.Native.shiftRight_six j
  unfold W.setTrit
  simp only [hq, ↓reduceIte]
  unfold bitOf
  generalize (1 : UInt64) <<< (j &&& 63).toUInt64 = b
  have hq13 : j / 64 < 13 := by omega
  generalize j / 64 = q at hq13 ⊢
  by_cases hl : l < 13
  · interval_cases q <;> interval_cases l <;> rfl
  · rw [W.limbM_ge _ (by omega), W.limbM_ge _ (by omega), ite_eq_right (by omega)]

theorem W.setTrit_other (a : W) (j : ℕ) {z : ℕ} (h1 : z ≠ 1) (h2 : z ≠ 2) : a.setTrit j z = a := by
  unfold W.setTrit
  simp only [h1, h2, ↓reduceIte]

theorem testBit_one_shift (j : ℕ) (t : ℕ) :
    ((1 : UInt64) <<< (j &&& 63).toUInt64).toNat.testBit t = decide (t = j % 64) := by
  have hj : j &&& 63 = j % 64 := by
    rw [show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have hs : ((j &&& 63).toUInt64).toNat % 64 = j % 64 := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', hj, Nat.mod_eq_of_lt (by omega : j % 64 < 2 ^ 64)]
    omega
  rw [UInt64.toNat_shiftLeft, hs, UInt64.toNat_one, Nat.testBit_mod_two_pow, Nat.one_shiftLeft,
    Nat.testBit_two_pow]
  by_cases h : t = j % 64
  · subst h; simp; omega
  · simp [h]
    intro _ h'
    exact h h'.symm

theorem testBit_bitOf (j t : ℕ) : (bitOf j).toNat.testBit t = decide (t = j % 64) :=
  testBit_one_shift j t

theorem W.bitP_setTrit (a : W) {j : ℕ} (hj : j < 832) (z i : ℕ) :
    (a.setTrit j z).bitP i = (a.bitP i || (decide (z = 1) && decide (i = j))) := by
  by_cases z1 : z = 1
  · subst z1
    rw [W.bitP_eq, W.bitP_eq, W.limbP_setTrit_one a hj]
    by_cases h : i / 64 = j / 64
    · rw [ite_eq_left h, UInt64.toNat_or, Nat.testBit_or, testBit_bitOf]
      have e : (i % 64 = j % 64) ↔ i = j := by omega
      simp [e]
    · rw [ite_eq_right h]
      have hij : i ≠ j := fun e => h (by rw [e])
      simp [hij]
  · by_cases z2 : z = 2
    · subst z2
      rw [W.bitP_eq, W.bitP_eq, W.limbP_setTrit_two a hj]
      simp
    · rw [W.setTrit_other a j z1 z2]
      simp [z1]

theorem W.bitM_setTrit (a : W) {j : ℕ} (hj : j < 832) (z i : ℕ) :
    (a.setTrit j z).bitM i = (a.bitM i || (decide (z = 2) && decide (i = j))) := by
  by_cases z2 : z = 2
  · subst z2
    rw [W.bitM_eq, W.bitM_eq, W.limbM_setTrit_two a hj]
    by_cases h : i / 64 = j / 64
    · rw [ite_eq_left h, UInt64.toNat_or, Nat.testBit_or, testBit_bitOf]
      have e : (i % 64 = j % 64) ↔ i = j := by omega
      simp [e]
    · rw [ite_eq_right h]
      have hij : i ≠ j := fun e => h (by rw [e])
      simp [hij]
  · by_cases z1 : z = 1
    · subst z1
      rw [W.bitM_eq, W.bitM_eq, W.limbM_setTrit_one a hj]
      simp
    · rw [W.setTrit_other a j z1 z2]
      simp [z2]

@[expose] def tritVal (z : ℕ) : ZMod 3 := if z = 1 then 1 else if z = 2 then 2 else 0

theorem W.val_setTrit {a : W} {j : ℕ} (hj : j < 832) (hz : a.val j = 0) (z i : ℕ) :
    (a.setTrit j z).val i = if i = j then tritVal z else a.val i := by
  unfold W.val
  rw [W.bitP_setTrit a hj, W.bitM_setTrit a hj]
  by_cases hij : i = j
  · subst hij
    have h0 : a.bitP i = false ∧ a.bitM i = false := by
      unfold W.val bitVal at hz
      split_ifs at hz with h1 h2
      · exact absurd hz (by decide)
      · exact absurd hz (by decide)
      · simp_all
    rw [h0.1, h0.2]
    unfold tritVal bitVal
    by_cases z1 : z = 1
    · simp [z1]
    · by_cases z2 : z = 2
      · simp [z2]
      · simp [z1, z2]
  · simp [hij]

theorem W.wf_setTrit {a : W} (ha : a.wf = true) {j : ℕ} (hj : j < 832) (hz : a.val j = 0)
    (z : ℕ) : (a.setTrit j z).wf = true := by
  apply W.wf_of_bits
  intro i
  rw [W.bitP_setTrit a hj, W.bitM_setTrit a hj]
  by_cases hij : i = j
  · subst hij
    have h0 : a.bitP i = false ∧ a.bitM i = false := by
      unfold W.val bitVal at hz
      split_ifs at hz with h1 h2
      · exact absurd hz (by decide)
      · exact absurd hz (by decide)
      · simp_all
    rw [h0.1, h0.2]
    by_cases z1 : z = 1
    · simp [z1]
    · simp [z1]
  · simp only [hij, decide_false, Bool.and_false, Bool.or_false]
    exact W.not_both ha i

end CFSG.Sporadic.Fi24.Native
