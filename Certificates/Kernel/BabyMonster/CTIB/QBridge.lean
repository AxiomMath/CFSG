module

public import CFSG.Certificates.Kernel.BabyMonster.Native.Q23
public import CFSG.Certificates.Kernel.BabyMonster.Native.Census
public import Mathlib.Data.Nat.Bitwise
public import Certificates.Data.CFSGNative.CTIB.Arith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.Monster.B.CTIB.Native

set_option exponentiation.threshold 1024

theorem xor_eq (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
theorem land_eq (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl
theorem shr_eq (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
theorem shl_eq (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl

local instance : Std.Commutative (· ^^ · : Bool → Bool → Bool) := ⟨Bool.xor_comm⟩

@[expose] def bx (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => bx f n ^^ f n

theorem bx_congr {f g : ℕ → Bool} : ∀ {n}, (∀ i < n, f i = g i) → bx f n = bx g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [bx, bx, bx_congr fun i hi => h i (by omega), h n (by omega)]

theorem bx_false {f : ℕ → Bool} : ∀ {n}, (∀ i < n, f i = false) → bx f n = false
  | 0, _ => rfl
  | n + 1, h => by rw [bx, bx_false fun i hi => h i (by omega), h n (by omega)]; rfl

theorem bx_add (f : ℕ → Bool) (m : ℕ) : ∀ n, bx f (m + n) = (bx f m ^^ bx (fun i => f (m + i)) n)
  | 0 => by simp [bx]
  | n + 1 => by rw [← Nat.add_assoc, bx, bx, bx_add f m n, Bool.xor_assoc]

theorem and_bx (b : Bool) (f : ℕ → Bool) : ∀ n, (b && bx f n) = bx (fun i => b && f i) n
  | 0 => by simp [bx]
  | n + 1 => by rw [bx, bx, ← and_bx b f n]; cases b <;> simp

theorem testBit_two_pow_sub_one' (n i : ℕ) : (2 ^ n - 1).testBit i = decide (i < n) :=
  Nat.testBit_two_pow_sub_one n i

theorem par32_bit (x : ℕ) : (par32 x).testBit 0 = bx x.testBit 32 := by
  have h65 : (65535 : ℕ) = 2 ^ 16 - 1 := rfl
  simp only [par32, xor_eq, land_eq, shr_eq, h65, Nat.testBit_xor, Nat.testBit_and,
    Nat.testBit_shiftRight, testBit_two_pow_sub_one', bx, Nat.testBit_one_zero]
  simp only [Nat.reduceAdd, Nat.reduceLT, decide_true, Bool.and_true, Bool.false_xor]
  ac_rfl

theorem par32_lt (x : ℕ) : par32 x < 2 := by
  have h : ∀ y : ℕ, Nat.land y 1 < 2 := fun y => lt_of_le_of_lt Nat.and_le_right (by decide)
  exact h _

@[expose] def wsum (c : ℕ → ℕ) (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ (k * n) * c n + wsum c k n

theorem wsum_lt {c : ℕ → ℕ} {k : ℕ} (hc : ∀ m, c m < 2 ^ k) : ∀ n, wsum c k n < 2 ^ (k * n)
  | 0 => by simp [wsum]
  | n + 1 => by
    have h := wsum_lt hc n
    have h2 : 2 ^ (k * (n + 1)) = 2 ^ (k * n) * 2 ^ k := by rw [Nat.mul_succ, Nat.pow_add]
    rw [wsum, h2]
    have := hc n
    have h3 : 2 ^ (k * n) * c n + 2 ^ (k * n) ≤ 2 ^ (k * n) * 2 ^ k := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ this
    omega

theorem testBit_wsum {c : ℕ → ℕ} {k : ℕ} (hc : ∀ m, c m < 2 ^ k) {r : ℕ} (hr : r < k) :
    ∀ n m, (wsum c k n).testBit (k * m + r) = (decide (m < n) && (c m).testBit r)
  | 0, m => by simp [wsum]
  | n + 1, m => by
    rw [wsum, Nat.testBit_two_pow_mul_add _ (wsum_lt hc n)]
    by_cases hm : m < n
    · have h1 : k * m + r < k * n := by
        have := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hm)
        rw [Nat.mul_succ] at this
        omega
      have hm' : m < n + 1 := by omega
      rw [ite_eq_left h1, testBit_wsum hc hr n m]
      simp [hm, hm']
    · have h1 : ¬ k * m + r < k * n := by
        have := Nat.mul_le_mul_left k (Nat.le_of_not_lt hm)
        omega
      rw [ite_eq_right h1]
      by_cases he : m = n
      · subst he
        simp
      · have h2 : k * m + r - k * n = k * (m - n) + r := by
          rw [Nat.mul_sub]
          have := Nat.mul_le_mul_left k (Nat.le_of_not_lt hm)
          omega
        have hlt : c n < 2 ^ (k * (m - n)) := lt_of_lt_of_le (hc n)
          (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (by omega)))
        rw [h2, Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))]
        have hm' : ¬ m < n + 1 := by omega
        simp [hm']

theorem testBit_wsum_ge {c : ℕ → ℕ} {k : ℕ} (hc : ∀ m, c m < 2 ^ k) {n p : ℕ}
    (hp : k * n ≤ p) : (wsum c k n).testBit p = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (wsum_lt hc n) (Nat.pow_le_pow_right (by decide) hp))

theorem testBit_wsum' {c : ℕ → ℕ} {k : ℕ} (hk : 0 < k) (hc : ∀ m, c m < 2 ^ k) (n p : ℕ) :
    (wsum c k n).testBit p = (decide (p / k < n) && (c (p / k)).testBit (p % k)) := by
  have e := Nat.div_add_mod p k
  conv_lhs => rw [← e]
  exact testBit_wsum hc (Nat.mod_lt _ hk) n _

theorem mul_wsum (v k : ℕ) : ∀ n, v * wsum (fun _ => 1) k n = wsum (fun _ => v) k n
  | 0 => rfl
  | n + 1 => by rw [wsum, wsum, Nat.mul_add, mul_wsum v k n, Nat.mul_one, Nat.mul_comm]

theorem wsum_mul (c : ℕ → ℕ) (k M : ℕ) : ∀ n, wsum c k n * M = wsum (fun m => c m * M) k n
  | 0 => by rw [wsum, wsum, Nat.zero_mul]
  | n + 1 => by rw [wsum, wsum, Nat.add_mul, wsum_mul c k M n, Nat.mul_assoc]

theorem SPR31_eq : SPR31 = wsum (fun _ => 1) 31 22 := by decide +kernel

theorem S32_eq : S32 = wsum (fun _ => 1) 32 22 := by decide +kernel

theorem one_lt_pow {k : ℕ} (hk : 0 < k) : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)

theorem spread_eq {v : ℕ} (hv : v < 2 ^ 22) :
    Nat.land (Nat.mul v SPR31) S32 = wsum (fun m => if v.testBit m then 1 else 0) 32 22 := by
  apply Nat.eq_of_testBit_eq
  intro p
  have hc1 : ∀ _ : ℕ, (1 : ℕ) < 2 ^ 32 := fun _ => one_lt_pow (by decide)
  have hcv : ∀ m : ℕ, (if v.testBit m then 1 else 0) < 2 ^ 32 := fun m => by
    split_ifs <;> exact lt_of_le_of_lt (by decide) (one_lt_pow (by decide))
  rw [land_eq, Nat.testBit_and, S32_eq, testBit_wsum' (by decide) hc1,
    testBit_wsum' (by decide) hcv]
  by_cases hm : p / 32 < 22
  · by_cases hr : p % 32 = 0
    · have hp : p = 31 * (p / 32) + p / 32 := by omega
      have hv31 : ∀ _ : ℕ, v < 2 ^ 31 := fun _ => lt_of_lt_of_le hv (by decide)
      have hmul : Nat.mul v SPR31 = v * SPR31 := rfl
      rw [hr, hmul, SPR31_eq, mul_wsum, hp, testBit_wsum hv31 (by omega)]
      rw [← hp]
      cases v.testBit (p / 32) <;> simp [hm]
    · have h1 : (1 : ℕ).testBit (p % 32) = false :=
        Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow hr)
      have h2 : ((if v.testBit (p / 32) then 1 else 0 : ℕ)).testBit (p % 32) = false := by
        split_ifs
        · exact h1
        · exact Nat.zero_testBit _
      rw [h1, h2]
      simp
  · simp [hm]

theorem blocks_eq {v : ℕ} (hv : v < 2 ^ 22) :
    Nat.mul (Nat.land (Nat.mul v SPR31) S32) 4294967295 =
      wsum (fun m => if v.testBit m then 2 ^ 32 - 1 else 0) 32 22 := by
  have hmul : ∀ a b : ℕ, Nat.mul a b = a * b := fun _ _ => rfl
  rw [hmul (Nat.land _ _), spread_eq hv, wsum_mul]
  congr 1
  funext m
  split_ifs <;> rfl

theorem testBit_blocks {v : ℕ} (hv : v < 2 ^ 22) (p : ℕ) :
    (Nat.mul (Nat.land (Nat.mul v SPR31) S32) 4294967295).testBit p =
      (decide (p / 32 < 22) && v.testBit (p / 32)) := by
  have hc : ∀ m : ℕ, (if v.testBit m then 2 ^ 32 - 1 else 0 : ℕ) < 2 ^ 32 := fun m => by
    split_ifs <;> decide
  rw [blocks_eq hv, testBit_wsum' (by decide) hc]
  cases h : v.testBit (p / 32)
  · simp
  · simp only [ite_true, testBit_two_pow_sub_one']
    have := Nat.mod_lt p (by decide : 0 < 32)
    simp [this]

theorem sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl

@[expose] noncomputable def fold5 (x : ℕ) : ℕ :=
  (fun x1 => (fun x2 => (fun x3 => (fun x4 =>
      Nat.xor (Nat.land x4 (nat_lit 4294967295)) (Nat.shiftRight x4 (nat_lit 32)))
    (Nat.xor (Nat.land x3 (nat_lit 18446744073709551615)) (Nat.shiftRight x3 (nat_lit 64))))
    (Nat.xor (Nat.land x2 (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 128)) (nat_lit 1)))
      (Nat.shiftRight x2 (nat_lit 128))))
    (Nat.xor (Nat.land x1 (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1)))
      (Nat.shiftRight x1 (nat_lit 256))))
  (Nat.xor (Nat.land x (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 512)) (nat_lit 1)))
    (Nat.shiftRight x (nat_lit 512)))

theorem xorFields_eq (LO v : ℕ) : xorFields LO v =
    fold5 (Nat.land LO (Nat.mul (Nat.land (Nat.mul v SPR31) S32) 4294967295)) := rfl

theorem fold5_bit (x : ℕ) {j : ℕ} (hj : j < 32) :
    (fold5 x).testBit j = bx (fun a => x.testBit (j + 32 * a)) 32 := by
  have h32 : (4294967295 : ℕ) = 2 ^ 32 - 1 := rfl
  have h64 : (18446744073709551615 : ℕ) = 2 ^ 64 - 1 := rfl
  simp only [fold5, xor_eq, land_eq, shr_eq, shl_eq, sub_eq, Nat.shiftLeft_eq, Nat.one_mul, h32,
    h64, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, testBit_two_pow_sub_one', bx]
  interval_cases j <;> simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, decide_true,
    Bool.and_true, Bool.false_xor] <;> ac_rfl

theorem xorFields_bit (LO : ℕ) {v : ℕ} (hv : v < 2 ^ 22) {j : ℕ} (hj : j < 32) :
    (xorFields LO v).testBit j =
      bx (fun m => decide (m < 22) && v.testBit m && LO.testBit (j + 32 * m)) 32 := by
  rw [xorFields_eq, fold5_bit _ hj]
  refine bx_congr fun m _ => ?_
  have hd : (j + 32 * m) / 32 = m := by omega
  rw [land_eq, Nat.testBit_and, testBit_blocks hv, hd, Bool.and_comm]

@[expose] def loOf (G : Array ℕ) : ℕ :=
  wsum (fun i => G.getD i 0 &&& (2 ^ i - 1) &&& (2 ^ 32 - 1)) 32 22

theorem loOf_lt (G : Array ℕ) (i : ℕ) : G.getD i 0 &&& (2 ^ i - 1) &&& (2 ^ 32 - 1) < 2 ^ 32 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

theorem loOf_bit (G : Array ℕ) {j : ℕ} (hj : j < 32) (m : ℕ) :
    (loOf G).testBit (j + 32 * m) =
      (decide (m < 22) && ((G.getD m 0).testBit j && decide (j < m))) := by
  have e : j + 32 * m = 32 * m + j := Nat.add_comm _ _
  rw [loOf, e, testBit_wsum (loOf_lt G) hj, Nat.testBit_and, Nat.testBit_and,
    testBit_two_pow_sub_one', testBit_two_pow_sub_one', decide_eq_true hj, Bool.and_true]

theorem cAtN_eq (gj u j : ℕ) : ∀ n, cAtN gj u j n =
    bx (fun i => decide (j < i) && u.testBit i && gj.testBit i) n
  | 0 => rfl
  | n + 1 => by rw [cAtN, bx, cAtN_eq gj u j n]

theorem corrN_eq (G : Array ℕ) (a b : ℕ) : ∀ m, corrN G a b m =
    bx (fun i => b.testBit i && cAt G a i) m
  | 0 => rfl
  | m + 1 => by
    rw [corrN, bx, ← corrN_eq G a b m]
    cases b.testBit m <;> simp

theorem M22_eq : (4194303 : ℕ) = 2 ^ 22 - 1 := rfl

theorem xorLo_bit (G : Array ℕ) (a : ℕ) {j : ℕ} (hj : j < 32) :
    (xorFields (loOf G) (Nat.land a 4194303)).testBit j =
      bx (fun m => decide (j < m) && a.testBit m && (G.getD m 0).testBit j) 22 := by
  have hv : Nat.land a 4194303 < 2 ^ 22 := lt_of_le_of_lt Nat.and_le_right (by decide)
  have h32 : (32 : ℕ) = 22 + 10 := rfl
  rw [xorFields_bit _ hv hj, h32, bx_add, bx_false (n := 10) fun i _ => by simp,
    Bool.xor_false]
  refine bx_congr fun m hm => ?_
  rw [land_eq, Nat.testBit_and, M22_eq, testBit_two_pow_sub_one', loOf_bit G hj]
  simp only [hm, decide_true, Bool.true_and, Bool.and_true]
  cases a.testBit m <;> cases (G.getD m 0).testBit j <;> cases decide (j < m) <;> rfl

theorem sign_eq (G : Array ℕ)
    (hG : ∀ i < 22, ∀ j < 22, (G.getD i 0).testBit j = (G.getD j 0).testBit i) (a b : ℕ) :
    (par32 (Nat.land (xorFields (loOf G) (Nat.land a 4194303)) b)).testBit 0 = corr G a b := by
  have h32 : (32 : ℕ) = 22 + 10 := rfl
  rw [par32_bit, corr, corrN_eq, h32, bx_add, bx_false (n := 10) fun i hi => ?_, Bool.xor_false]
  · refine bx_congr fun j hj => ?_
    rw [land_eq, Nat.testBit_and, xorLo_bit G a (by omega), Bool.and_comm, cAt, cAtN_eq]
    congr 1
    refine bx_congr fun m hm => ?_
    rw [hG m hm j hj]
  · rw [land_eq, Nat.testBit_and, xorLo_bit G a (by omega),
      bx_false fun m hm => by simp; omega, Bool.false_and]

theorem mulQ_loOf (G : Array ℕ)
    (hG : ∀ i < 22, ∀ j < 22, (G.getD i 0).testBit j = (G.getD j 0).testBit i) (a b : ℕ) :
    mulQ (loOf G) a b = qmul G a b := by
  have hs := sign_eq G hG a b
  have hdef : mulQ (loOf G) a b = ((a ^^^ b) &&& (2 ^ 22 - 1)) ||| ((((a ^^^ b) >>> 22) ^^^
      par32 (Nat.land (xorFields (loOf G) (Nat.land a 4194303)) b)) &&& (2 ^ 1 - 1)) <<< 22 :=
    rfl
  rw [hdef]
  generalize par32 (Nat.land (xorFields (loOf G) (Nat.land a 4194303)) b) = S at hs ⊢
  rw [qmul, ← hs]
  apply Nat.eq_of_testBit_eq
  intro p
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_xor,
    Nat.testBit_shiftRight, testBit_two_pow_sub_one', Nat.testBit_mod_two_pow]
  rcases Nat.lt_trichotomy p 22 with hp | rfl | hp
  · have h1 : ¬ p ≥ 22 := by omega
    have hn : ¬ 22 = p := by omega
    split_ifs <;> simp only [Nat.testBit_two_pow, Nat.zero_testBit] <;> simp [hp, h1, hn]
  · have e : (22 : ℕ) + 0 = 22 := rfl
    simp only [Nat.sub_self, e, Nat.lt_irrefl, decide_false, Bool.and_false, Bool.false_or,
      ge_iff_le, Nat.le_refl, decide_true, Bool.true_and, Nat.zero_lt_one, Bool.and_true]
    split_ifs with h <;> simp only [Nat.testBit_two_pow, Nat.zero_testBit, decide_true]
    · exact h
    · exact Bool.eq_false_iff.2 h
  · have h1 : ¬ p < 22 := by omega
    have hq : ¬ p - 22 < 1 := by omega
    have hn : ¬ 22 = p := by omega
    split_ifs <;> simp only [Nat.testBit_two_pow, Nat.zero_testBit] <;> simp [h1, hq, hn]

theorem forceB_eq (v : ℕ) (k : ℕ → ℕ) : forceB v k = k v := by
  unfold forceB
  cases Nat.beq v 0 <;> rfl

@[expose] noncomputable def arrOf (A : ℕ) : Array ℕ := ((List.range 22).map (fld32 A)).toArray

theorem arrOf_getD (A : ℕ) {i : ℕ} (hi : i < 22) : (arrOf A).getD i 0 = fld32 A i := by
  simp [arrOf, hi]

@[expose] noncomputable def autQR (LO : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ out => out)
    (fun _ ih Ar v out => forceB (Bool.rec (motive := fun _ => Nat)
        (mulQ LO out (Nat.land Ar (nat_lit 4294967295))) out
        (Nat.beq (Nat.land v (nat_lit 1)) (nat_lit 0)))
      (fun o => ih (Nat.shiftRight Ar (nat_lit 32)) (Nat.shiftRight v (nat_lit 1)) o)) k

theorem autQ_eq (LO A n : ℕ) :
    autQ LO A n = autQR LO 22 A (Nat.land n 4194303) (Nat.land n 4194304) := rfl

theorem autQR_succ (LO k Ar v out : ℕ) : autQR LO (k + 1) Ar v out =
    autQR LO k (Ar >>> 32) (v >>> 1)
      (if (v &&& 1) = 0 then out else mulQ LO out (Ar &&& (2 ^ 32 - 1))) := by
  have e : autQR LO (k + 1) Ar v out = forceB (Bool.rec (motive := fun _ => Nat)
      (mulQ LO out (Nat.land Ar 4294967295)) out (Nat.beq (Nat.land v 1) 0))
      (fun o => autQR LO k (Nat.shiftRight Ar 32) (Nat.shiftRight v 1) o) := rfl
  rw [e, forceB_eq]
  by_cases h : (v &&& 1) = 0
  · have hb : Nat.beq (Nat.land v 1) 0 = true := Nat.beq_eq_true_eq _ _ ▸ h
    rw [hb, ite_eq_left h]
    rfl
  · have hb : Nat.beq (Nat.land v 1) 0 = false := Bool.eq_false_iff.2 fun h' =>
      h (Nat.eq_of_beq_eq_true h')
    rw [hb, ite_eq_right h]
    rfl

theorem fld32_eq (A i : ℕ) : fld32 A i = (A >>> (32 * i)) &&& (2 ^ 32 - 1) := rfl

theorem autQR_spec (G : Array ℕ)
    (hG : ∀ i < 22, ∀ j < 22, (G.getD i 0).testBit j = (G.getD j 0).testBit i) (A n : ℕ) :
    ∀ k i, i + k = 22 → autQR (loOf G) k (A >>> (32 * i)) ((n &&& (2 ^ 22 - 1)) >>> i)
      (autApplyN G (arrOf A) n i) = autApply G (arrOf A) n
  | 0, i, h => by
    rw [Nat.add_zero] at h
    subst h
    rfl
  | k + 1, i, h => by
    rw [autQR_succ, ← Nat.shiftRight_add, ← Nat.mul_succ, ← Nat.shiftRight_add]
    have hi : i < 22 := by omega
    have hbit : ((n &&& (2 ^ 22 - 1)) >>> i &&& 1 = 0) ↔ n.testBit i = false := by
      have ht : (n &&& (2 ^ 22 - 1)).testBit i = n.testBit i := by
        rw [Nat.testBit_and, testBit_two_pow_sub_one', decide_eq_true hi, Bool.and_true]
      rw [← ht, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
      simp
    have hstep : (if ((n &&& (2 ^ 22 - 1)) >>> i &&& 1) = 0 then autApplyN G (arrOf A) n i else
        mulQ (loOf G) (autApplyN G (arrOf A) n i) ((A >>> (32 * i)) &&& (2 ^ 32 - 1))) =
        autApplyN G (arrOf A) n (i + 1) := by
      rw [autApplyN, mulQ_loOf G hG, ← fld32_eq, ← arrOf_getD A hi]
      by_cases hb : n.testBit i
      · rw [ite_eq_right (fun h => by simp [(hbit.1 h)] at hb), ite_eq_left hb]
      · rw [ite_eq_left (hbit.2 (Bool.eq_false_iff.2 hb)), ite_eq_right hb]
    rw [hstep]
    exact autQR_spec G hG A n k (i + 1) (by omega)

theorem autQ_loOf (G : Array ℕ)
    (hG : ∀ i < 22, ∀ j < 22, (G.getD i 0).testBit j = (G.getD j 0).testBit i) (A n : ℕ) :
    autQ (loOf G) A n = autApply G (arrOf A) n := by
  have h := autQR_spec G hG A n 22 0 rfl
  rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.shiftRight_zero] at h
  rw [autQ_eq, ← h]
  congr 1
  have e : (4194304 : ℕ) = 2 ^ 22 := rfl
  rw [land_eq, e, Nat.and_two_pow, autApplyN]
  cases n.testBit 22 <;> simp

theorem qmul_lt (G : Array ℕ) (a b : ℕ) : qmul G a b < 2 ^ 23 := by
  rw [qmul]
  refine Nat.or_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)) ?_
  split_ifs <;> decide

theorem autApplyN_lt (G A : Array ℕ) (n : ℕ) : ∀ m, autApplyN G A n m < 2 ^ 23
  | 0 => by rw [autApplyN]; split_ifs <;> decide
  | m + 1 => by
    rw [autApplyN]
    split_ifs
    · exact qmul_lt G _ _
    · exact autApplyN_lt G A n m

theorem autApply_lt (G A : Array ℕ) (n : ℕ) : autApply G A n < 2 ^ 23 := autApplyN_lt G A n 22

@[expose] noncomputable def compR (LO B : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih Ar sh acc =>
      forceB (Nat.lor acc (Nat.shiftLeft (autQ LO B (Nat.land Ar (nat_lit 4294967295))) sh))
      (fun a => ih (Nat.shiftRight Ar (nat_lit 32)) (Nat.add sh (nat_lit 32)) a)) k

theorem compAut_eq (LO A B : ℕ) : compAut LO A B = compR LO B 22 A 0 0 := rfl

theorem compR_succ (LO B k Ar sh acc : ℕ) : compR LO B (k + 1) Ar sh acc =
    compR LO B k (Ar >>> 32) (sh + 32) (acc ||| (autQ LO B (Ar &&& (2 ^ 32 - 1)) <<< sh)) := by
  have e : compR LO B (k + 1) Ar sh acc =
      forceB (Nat.lor acc (Nat.shiftLeft (autQ LO B (Nat.land Ar 4294967295)) sh))
        (fun a => compR LO B k (Nat.shiftRight Ar 32) (Nat.add sh 32) a) := rfl
  rw [e, forceB_eq]
  rfl

theorem or_shiftLeft_eq {x n : ℕ} (hx : x < 2 ^ n) (y : ℕ) : x ||| (y <<< n) = 2 ^ n * y + x := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_mul_add _ hx]
  by_cases hp : p < n
  · have hp' : ¬ p ≥ n := by omega
    simp [hp, hp']
  · have hlt : x.testBit p = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    have hp' : p ≥ n := by omega
    simp [hp, hp', hlt]

theorem compR_spec (G : Array ℕ)
    (hG : ∀ i < 22, ∀ j < 22, (G.getD i 0).testBit j = (G.getD j 0).testBit i) (A B : ℕ) :
    ∀ k i, i + k = 22 → compR (loOf G) B k (A >>> (32 * i)) (32 * i)
      (wsum (fun t => autQ (loOf G) B (fld32 A t)) 32 i) =
      wsum (fun t => autQ (loOf G) B (fld32 A t)) 32 22
  | 0, i, h => by
    rw [Nat.add_zero] at h
    subst h
    rfl
  | k + 1, i, h => by
    have hV : ∀ t, autQ (loOf G) B (fld32 A t) < 2 ^ 32 := fun t => by
      rw [autQ_loOf G hG]
      exact lt_of_lt_of_le (autApply_lt _ _ _) (by decide)
    rw [compR_succ, ← Nat.shiftRight_add, ← fld32_eq, or_shiftLeft_eq (wsum_lt hV i)]
    have e1 : 32 * i + 32 = 32 * (i + 1) := by ring
    have e2 : 2 ^ (32 * i) * autQ (loOf G) B (fld32 A i) +
        wsum (fun t => autQ (loOf G) B (fld32 A t)) 32 i =
        wsum (fun t => autQ (loOf G) B (fld32 A t)) 32 (i + 1) := rfl
    rw [e1, e2]
    exact compR_spec G hG A B k (i + 1) (by omega)

theorem fld32_wsum {V : ℕ → ℕ} (hV : ∀ t, V t < 2 ^ 32) {i : ℕ} (hi : i < 22) :
    fld32 (wsum V 32 22) i = V i := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [fld32_eq, Nat.testBit_and, Nat.testBit_shiftRight, testBit_two_pow_sub_one']
  by_cases hr : r < 32
  · rw [testBit_wsum hV hr]
    simp [hr, hi]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hV i)
      (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp [hr]

theorem compAut_loOf (G : Array ℕ)
    (hG : ∀ i < 22, ∀ j < 22, (G.getD i 0).testBit j = (G.getD j 0).testBit i) (A B : ℕ) :
    arrOf (compAut (loOf G) A B) = autComp G (arrOf A) (arrOf B) := by
  have hV : ∀ t, autQ (loOf G) B (fld32 A t) < 2 ^ 32 := fun t => by
    rw [autQ_loOf G hG]
    exact lt_of_lt_of_le (autApply_lt _ _ _) (by decide)
  have h := compR_spec G hG A B 22 0 rfl
  rw [Nat.mul_zero, Nat.shiftRight_zero, wsum] at h
  rw [compAut_eq, h, autComp]
  unfold arrOf
  rw [List.map_toArray, List.map_map]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  rw [Function.comp_apply, fld32_wsum hV (List.mem_range.1 hi), autQ_loOf G hG]
  rfl

end CertificateChecks.KernelBM.CTIB

end
