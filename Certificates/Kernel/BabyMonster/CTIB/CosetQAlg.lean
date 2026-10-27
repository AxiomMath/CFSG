module

public import Certificates.Kernel.BabyMonster.CTIB.QBridge

public section

namespace CertificateChecks.KernelBM.CTIB.CosetQ

open CFSG.Monster.B.CTIB.Native CertificateChecks.KernelBM.CTIB

local instance : Std.Commutative (· ^^ · : Bool → Bool → Bool) := ⟨Bool.xor_comm⟩
local instance : Std.Associative (· ^^ · : Bool → Bool → Bool) := ⟨Bool.xor_assoc⟩

theorem bx_xor (f g : ℕ → Bool) : ∀ n, bx (fun i => f i ^^ g i) n = (bx f n ^^ bx g n)
  | 0 => rfl
  | n + 1 => by
    rw [bx, bx, bx, bx_xor f g n]
    cases bx f n <;> cases bx g n <;> cases f n <;> cases g n <;> rfl

theorem bx_and (f : ℕ → Bool) (b : Bool) (n : ℕ) : (bx f n && b) = bx (fun i => f i && b) n := by
  rw [Bool.and_comm, and_bx]
  exact bx_congr fun i _ => Bool.and_comm _ _

theorem bx_comm (F : ℕ → ℕ → Bool) (n : ℕ) : ∀ m,
    bx (fun i => bx (F i) n) m = bx (fun j => bx (fun i => F i j) m) n
  | 0 => (bx_false fun _ _ => rfl).symm
  | m + 1 => by
    rw [bx, bx_comm F n m, ← bx_xor]
    rfl

theorem bx_single (f : ℕ → Bool) (j : ℕ) : ∀ n,
    bx (fun i => decide (j = i) && f i) n = (decide (j < n) && f j)
  | 0 => by simp [bx]
  | n + 1 => by
    rw [bx, bx_single f j n]
    rcases Nat.lt_trichotomy j n with h | rfl | h
    · have h1 : j < n + 1 := by omega
      simp [h, h1, Nat.ne_of_lt h]
    · simp
    · have h1 : ¬ j < n + 1 := by omega
      have h2 : ¬ j < n := by omega
      simp [h1, h2, Nat.ne_of_gt h]

theorem bx_tri (f : ℕ → Bool) {s n : ℕ} (h : s ≤ n) :
    bx f s = bx (fun j => decide (j < s) && f j) n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [bx_add, bx_false (n := d) fun i _ => by
    rw [decide_eq_false (by omega : ¬ s + i < s), Bool.false_and], Bool.xor_false]
  exact bx_congr fun i hi => by simp [hi]

@[expose] def dsum (F : ℕ → ℕ → Bool) : Bool := bx (fun s => bx (F s) 22) 22

theorem dsum_xor (F H : ℕ → ℕ → Bool) :
    dsum (fun s t => F s t ^^ H s t) = (dsum F ^^ dsum H) := by
  unfold dsum
  rw [← bx_xor]
  exact bx_congr fun s _ => bx_xor _ _ 22

theorem dsum_congr {F H : ℕ → ℕ → Bool} (h : ∀ s < 22, ∀ t < 22, F s t = H s t) :
    dsum F = dsum H :=
  bx_congr fun s hs => bx_congr fun t ht => h s hs t ht

theorem dsum_false {F : ℕ → ℕ → Bool} (h : ∀ s < 22, ∀ t < 22, F s t = false) : dsum F = false :=
  bx_false fun s hs => bx_false fun t ht => h s hs t ht

theorem dsum_swap (F : ℕ → ℕ → Bool) : dsum F = dsum (fun t s => F s t) :=
  bx_comm F 22 22

@[expose] def bil (F : ℕ → ℕ → Bool) (a b : ℕ → Bool) : Bool :=
  bx (fun t => bx (fun j => a j && b t && F j t) 22) 22

theorem bil_congr {F : ℕ → ℕ → Bool} {a a' b b' : ℕ → Bool} (ha : ∀ j < 22, a j = a' j)
    (hb : ∀ t < 22, b t = b' t) : bil F a b = bil F a' b' :=
  bx_congr fun t ht => bx_congr fun j hj => by rw [ha j hj, hb t ht]

theorem bil_zero_left (F : ℕ → ℕ → Bool) (b : ℕ → Bool) : bil F (fun _ => false) b = false :=
  bx_false fun _ _ => bx_false fun _ _ => rfl

theorem bil_zero_right (F : ℕ → ℕ → Bool) (a : ℕ → Bool) : bil F a (fun _ => false) = false :=
  bx_false fun _ _ => bx_false fun _ _ => by simp

theorem bil_xor_left (F : ℕ → ℕ → Bool) (a a' b : ℕ → Bool) :
    bil F (fun j => a j ^^ a' j) b = (bil F a b ^^ bil F a' b) := by
  unfold bil
  rw [← bx_xor]
  refine bx_congr fun t _ => ?_
  rw [← bx_xor]
  refine bx_congr fun j _ => ?_
  beta_reduce
  cases a j <;> cases a' j <;> cases b t <;> cases F j t <;> rfl

theorem bil_xor_right (F : ℕ → ℕ → Bool) (a b b' : ℕ → Bool) :
    bil F a (fun t => b t ^^ b' t) = (bil F a b ^^ bil F a b') := by
  unfold bil
  rw [← bx_xor]
  refine bx_congr fun t _ => ?_
  rw [← bx_xor]
  refine bx_congr fun j _ => ?_
  beta_reduce
  cases a j <;> cases b t <;> cases b' t <;> cases F j t <;> rfl

theorem bil_and_left (F : ℕ → ℕ → Bool) (x : Bool) (a b : ℕ → Bool) :
    bil F (fun j => x && a j) b = (x && bil F a b) := by
  cases x
  · exact bil_zero_left F b
  · rfl

theorem bil_and_right (F : ℕ → ℕ → Bool) (x : Bool) (a b : ℕ → Bool) :
    bil F a (fun t => x && b t) = (x && bil F a b) := by
  cases x
  · exact bil_zero_right F a
  · rfl

theorem bil_sum_left (F : ℕ → ℕ → Bool) (c : ℕ → Bool) (V : ℕ → ℕ → Bool) (b : ℕ → Bool) :
    ∀ m, bil F (fun j => bx (fun s => c s && V s j) m) b = bx (fun s => c s && bil F (V s) b) m
  | 0 => bil_zero_left F b
  | m + 1 => by
    have e : (fun j => bx (fun s => c s && V s j) (m + 1)) =
        fun j => bx (fun s => c s && V s j) m ^^ (c m && V m j) := rfl
    rw [e, bil_xor_left, bil_sum_left F c V b m, bil_and_left, bx]

theorem bil_sum_right (F : ℕ → ℕ → Bool) (a : ℕ → Bool) (c : ℕ → Bool) (V : ℕ → ℕ → Bool) :
    ∀ m, bil F a (fun t => bx (fun s => c s && V s t) m) = bx (fun s => c s && bil F a (V s)) m
  | 0 => bil_zero_right F a
  | m + 1 => by
    have e : (fun t => bx (fun s => c s && V s t) (m + 1)) =
        fun t => bx (fun s => c s && V s t) m ^^ (c m && V m t) := rfl
    rw [e, bil_xor_right, bil_sum_right F a c V m, bil_and_right, bx]

theorem bil_single (F : ℕ → ℕ → Bool) {i j : ℕ} (hi : i < 22) (hj : j < 22) :
    bil F (fun x => decide (i = x)) (fun x => decide (j = x)) = F i j := by
  unfold bil
  have h1 : ∀ t, bx (fun x => decide (i = x) && decide (j = t) && F x t) 22 =
      (decide (j = t) && F i t) := fun t => by
    rw [bx_congr (n := 22) (g := fun x => decide (i = x) && (decide (j = t) && F x t))
      (fun x _ => Bool.and_assoc _ _ _), bx_single, decide_eq_true hi, Bool.true_and]
  simp only [h1]
  rw [bx_single, decide_eq_true hj, Bool.true_and]

@[expose] def gam (G : Array ℕ) (j t : ℕ) : Bool := decide (t < j) && (G.getD t 0).testBit j

theorem corr_eq_bil (G : Array ℕ) (a b : ℕ) : corr G a b = bil (gam G) a.testBit b.testBit := by
  rw [corr, corrN_eq]
  refine bx_congr fun t _ => ?_
  rw [cAt, cAtN_eq, and_bx]
  refine bx_congr fun j _ => ?_
  unfold gam
  cases a.testBit j <;> cases b.testBit t <;> cases decide (t < j) <;>
    cases (G.getD t 0).testBit j <;> rfl

theorem corr_congr (G : Array ℕ) {a a' b b' : ℕ} (ha : ∀ j < 22, a.testBit j = a'.testBit j)
    (hb : ∀ t < 22, b.testBit t = b'.testBit t) : corr G a b = corr G a' b' := by
  rw [corr_eq_bil, corr_eq_bil]
  exact bil_congr ha hb

theorem corr_xor_left (G : Array ℕ) (a a' b : ℕ) :
    corr G (a ^^^ a') b = (corr G a b ^^ corr G a' b) := by
  rw [corr_eq_bil, corr_eq_bil, corr_eq_bil, ← bil_xor_left]
  exact bil_congr (fun j _ => Nat.testBit_xor _ _ _) fun _ _ => rfl

theorem corr_zero_left (G : Array ℕ) (b : ℕ) : corr G 0 b = false := by
  rw [corr_eq_bil]
  exact (bil_congr (fun j _ => Nat.zero_testBit j) fun _ _ => rfl).trans (bil_zero_left _ _)

theorem corr_two_pow (G : Array ℕ) {i j : ℕ} (hi : i < 22) (hj : j < 22) :
    corr G (2 ^ i) (2 ^ j) = gam G i j := by
  rw [corr_eq_bil]
  have e1 : (2 ^ i).testBit = fun x => decide (i = x) := funext fun x => Nat.testBit_two_pow
  have e2 : (2 ^ j).testBit = fun x => decide (j = x) := funext fun x => Nat.testBit_two_pow
  rw [e1, e2, bil_single _ hi hj]

theorem qmul_bit (G : Array ℕ) (a b : ℕ) {i : ℕ} (hi : i < 22) :
    (qmul G a b).testBit i = (a.testBit i ^^ b.testBit i) := by
  rw [qmul, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_xor, decide_eq_true hi,
    Bool.true_and]
  split_ifs
  · rw [Nat.testBit_two_pow_of_ne (by omega), Bool.or_false]
  · rw [Nat.zero_testBit, Bool.or_false]

theorem qmul_bit22 (G : Array ℕ) (a b : ℕ) :
    (qmul G a b).testBit 22 = ((a.testBit 22 ^^ b.testBit 22) ^^ corr G a b) := by
  rw [qmul, Nat.testBit_or, Nat.testBit_mod_two_pow]
  simp only [Nat.lt_irrefl, decide_false, Bool.false_and, Bool.false_or]
  split_ifs with h
  · rw [Nat.testBit_two_pow_self, h]
  · rw [Nat.zero_testBit]
    exact (Bool.eq_false_iff.2 h).symm

theorem code_ext {x y : ℕ} (hx : x < 2 ^ 23) (hy : y < 2 ^ 23)
    (h : ∀ i < 22, x.testBit i = y.testBit i) (h22 : x.testBit 22 = y.testBit 22) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases Nat.lt_trichotomy i 22 with hi | rfl | hi
  · exact h i hi
  · exact h22
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hi))]

theorem corr_qmul_left (G : Array ℕ) (a b c : ℕ) :
    corr G (qmul G a b) c = (corr G a c ^^ corr G b c) := by
  rw [← corr_xor_left]
  exact corr_congr G (fun j hj => by rw [qmul_bit G a b hj, Nat.testBit_xor]) fun _ _ => rfl

theorem corr_xor_right (G : Array ℕ) (a b b' : ℕ) :
    corr G a (b ^^^ b') = (corr G a b ^^ corr G a b') := by
  rw [corr_eq_bil, corr_eq_bil, corr_eq_bil, ← bil_xor_right]
  exact bil_congr (fun _ _ => rfl) fun t _ => Nat.testBit_xor _ _ _

theorem corr_qmul_right (G : Array ℕ) (a b c : ℕ) :
    corr G a (qmul G b c) = (corr G a b ^^ corr G a c) := by
  rw [← corr_xor_right]
  exact corr_congr G (fun _ _ => rfl) fun j hj => by rw [qmul_bit G b c hj, Nat.testBit_xor]

theorem qmul_assoc (G : Array ℕ) (a b c : ℕ) :
    qmul G (qmul G a b) c = qmul G a (qmul G b c) := by
  refine code_ext (qmul_lt G _ _) (qmul_lt G _ _) (fun i hi => ?_) ?_
  · rw [qmul_bit G _ _ hi, qmul_bit G _ _ hi, qmul_bit G _ _ hi, qmul_bit G _ _ hi,
      Bool.xor_assoc]
  · rw [qmul_bit22, qmul_bit22, qmul_bit22, qmul_bit22, corr_qmul_left, corr_qmul_right]
    ac_rfl

theorem qmul_zero_left (G : Array ℕ) {b : ℕ} (hb : b < 2 ^ 23) : qmul G 0 b = b := by
  refine code_ext (qmul_lt G _ _) hb (fun i hi => ?_) ?_
  · rw [qmul_bit G _ _ hi, Nat.zero_testBit, Bool.false_xor]
  · rw [qmul_bit22, Nat.zero_testBit, corr_zero_left, Bool.false_xor, Bool.xor_false]

theorem corr_zero_right (G : Array ℕ) (a : ℕ) : corr G a 0 = false := by
  rw [corr_eq_bil]
  exact (bil_congr (fun _ _ => rfl) fun j _ => Nat.zero_testBit j).trans (bil_zero_right _ _)

theorem qmul_zero_right (G : Array ℕ) {a : ℕ} (ha : a < 2 ^ 23) : qmul G a 0 = a := by
  refine code_ext (qmul_lt G _ _) ha (fun i hi => ?_) ?_
  · rw [qmul_bit G _ _ hi, Nat.zero_testBit, Bool.xor_false]
  · rw [qmul_bit22, Nat.zero_testBit, corr_zero_right, Bool.xor_false, Bool.xor_false]

@[expose] def qinvG (G : Array ℕ) (a : ℕ) : ℕ := qmul G (qmul G a a) a

theorem sq_sq (G : Array ℕ) (a : ℕ) : qmul G (qmul G a a) (qmul G a a) = 0 := by
  refine code_ext (qmul_lt G _ _) (by decide) (fun i hi => ?_) ?_
  · rw [qmul_bit G _ _ hi, qmul_bit G _ _ hi, Nat.zero_testBit]
    cases a.testBit i <;> rfl
  · rw [qmul_bit22, Nat.zero_testBit,
      corr_congr G (b := qmul G a a) (a' := 0) (b' := qmul G a a)
        (fun j hj => by rw [qmul_bit G _ _ hj, Nat.zero_testBit, Bool.xor_self]) fun _ _ => rfl,
      corr_zero_left, Bool.xor_self, Bool.xor_false]

theorem qinvG_mul (G : Array ℕ) (a : ℕ) : qmul G (qinvG G a) a = 0 := by
  rw [qinvG, qmul_assoc G (qmul G a a) a a, sq_sq]

theorem mul_qinvG (G : Array ℕ) (a : ℕ) : qmul G a (qinvG G a) = 0 := by
  rw [qinvG, ← qmul_assoc G a (qmul G a a) a, ← qmul_assoc G a a a,
    qmul_assoc G (qmul G a a) a a, sq_sq]

@[expose] def QC (_ : Array ℕ) : Type := {n : ℕ // n < 2 ^ 23}

instance (G : Array ℕ) : Group (QC G) where
  mul a b := ⟨qmul G a.1 b.1, qmul_lt G _ _⟩
  mul_assoc a b c := Subtype.ext (qmul_assoc G a.1 b.1 c.1)
  one := ⟨0, by decide⟩
  one_mul a := Subtype.ext (qmul_zero_left G a.2)
  mul_one a := Subtype.ext (qmul_zero_right G a.2)
  inv a := ⟨qinvG G a.1, qmul_lt G _ _⟩
  inv_mul_cancel a := Subtype.ext (qinvG_mul G a.1)

theorem QC.mul_val {G : Array ℕ} (a b : QC G) : (a * b).1 = qmul G a.1 b.1 := rfl

theorem QC.one_val {G : Array ℕ} : (1 : QC G).1 = 0 := rfl

theorem QC.inv_val {G : Array ℕ} (a : QC G) : a⁻¹.1 = qinvG G a.1 := rfl

@[expose] def cc (G A : Array ℕ) (j s : ℕ) : Bool := corr G (A.getD j 0) (A.getD s 0)

theorem autApplyN_bits (G A : Array ℕ) (n : ℕ) : ∀ m,
    (∀ i < 22, (autApplyN G A n m).testBit i =
      bx (fun s => n.testBit s && (A.getD s 0).testBit i) m) ∧
    (autApplyN G A n m).testBit 22 =
      ((n.testBit 22 ^^ bx (fun s => n.testBit s && (A.getD s 0).testBit 22) m) ^^
        bx (fun s => n.testBit s && bx (fun j => n.testBit j && cc G A j s) s) m)
  | 0 => by
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [autApplyN]
      split_ifs
      · rw [Nat.testBit_two_pow_of_ne (by omega)]
        rfl
      · rw [Nat.zero_testBit]
        rfl
    · rw [autApplyN]
      split_ifs with h
      · rw [Nat.testBit_two_pow_self, h]
        rfl
      · rw [Nat.zero_testBit, Bool.eq_false_iff.2 h]
        rfl
  | m + 1 => by
    obtain ⟨h1, h2⟩ := autApplyN_bits G A n m
    rw [autApplyN]
    by_cases hm : n.testBit m
    · rw [ite_eq_left hm]
      have hc : corr G (autApplyN G A n m) (A.getD m 0) =
          bx (fun j => n.testBit j && cc G A j m) m := by
        rw [corr_eq_bil, bil_congr h1 (fun _ _ => rfl), bil_sum_left]
        refine bx_congr fun j _ => ?_
        rw [cc, corr_eq_bil]
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [qmul_bit G _ _ hi, h1 i hi, bx, hm, Bool.true_and]
      · rw [qmul_bit22, h2, hc, bx, bx, hm, Bool.true_and, Bool.true_and]
        ac_rfl
    · rw [ite_eq_right hm]
      have hf : n.testBit m = false := Bool.eq_false_iff.2 hm
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [h1 i hi, bx, hf, Bool.false_and, Bool.xor_false]
      · rw [h2, bx, bx, hf, Bool.false_and, Bool.false_and, Bool.xor_false, Bool.xor_false]

@[expose] def quadA (G A : Array ℕ) (n : ℕ) : Bool :=
  dsum (fun s j => n.testBit s && n.testBit j && decide (j < s) && cc G A j s)

theorem autApply_bit (G A : Array ℕ) (n : ℕ) {i : ℕ} (hi : i < 22) :
    (autApply G A n).testBit i = bx (fun s => n.testBit s && (A.getD s 0).testBit i) 22 :=
  (autApplyN_bits G A n 22).1 i hi

theorem autApply_bit22 (G A : Array ℕ) (n : ℕ) :
    (autApply G A n).testBit 22 =
      ((n.testBit 22 ^^ bx (fun s => n.testBit s && (A.getD s 0).testBit 22) 22) ^^
        quadA G A n) := by
  rw [autApply, (autApplyN_bits G A n 22).2]
  congr 1
  refine bx_congr fun s hs => ?_
  rw [bx_tri _ (Nat.le_of_lt hs), and_bx]
  refine bx_congr fun j _ => ?_
  beta_reduce
  cases n.testBit s <;> cases n.testBit j <;> cases decide (j < s) <;> cases cc G A j s <;> rfl

@[expose] def RelOK (G A : Array ℕ) : Prop :=
  (∀ i < 22, cc G A i i = false) ∧
    ∀ i < 22, ∀ j < 22, (cc G A i j ^^ cc G A j i) = (gam G i j ^^ gam G j i)

theorem quadA_bits {G A : Array ℕ} {n n' : ℕ} (h : ∀ i < 22, n.testBit i = n'.testBit i) :
    quadA G A n = quadA G A n' :=
  dsum_congr fun s hs t ht => by rw [h s hs, h t ht]

theorem cross_eq {G A : Array ℕ} (hA : RelOK G A) (a b : ℕ) :
    ((corr G a b ^^ dsum (fun s j => a.testBit s && b.testBit j && decide (j < s) && cc G A j s)) ^^
      dsum (fun s j => b.testBit s && a.testBit j && decide (j < s) && cc G A j s)) =
      dsum (fun s t => a.testBit s && b.testBit t && cc G A s t) := by
  rw [corr_eq_bil]
  have e1 : bil (gam G) a.testBit b.testBit =
      dsum (fun x y => a.testBit x && b.testBit y && gam G x y) := by
    unfold bil
    exact dsum_swap _
  have e2 : dsum (fun s j => b.testBit s && a.testBit j && decide (j < s) && cc G A j s) =
      dsum (fun x y => a.testBit x && b.testBit y && decide (x < y) && cc G A x y) := by
    rw [dsum_swap]
    exact dsum_congr fun x _ y _ => by
      cases a.testBit x <;> cases b.testBit y <;> rfl
  rw [e1, e2, ← dsum_xor, ← dsum_xor]
  refine dsum_congr fun x hx y hy => ?_
  generalize (a.testBit x && b.testBit y) = p
  rcases Nat.lt_trichotomy x y with hxy | rfl | hxy
  · have g0 : gam G x y = false := by simp [gam, Nat.lt_asymm hxy]
    rw [g0, decide_eq_false (Nat.lt_asymm hxy), decide_eq_true hxy]
    cases p <;> simp
  · have g0 : gam G x x = false := by simp [gam]
    rw [g0, hA.1 x hx]
    cases p <;> simp
  · have hr := hA.2 x hx y hy
    have g1 : gam G y x = false := by simp [gam, Nat.lt_asymm hxy]
    rw [g1, Bool.xor_false] at hr
    rw [decide_eq_true hxy, decide_eq_false (Nat.lt_asymm hxy), ← hr]
    cases p <;> cases cc G A x y <;> cases cc G A y x <;> rfl

theorem quadA_qmul (G A : Array ℕ) (a b : ℕ) :
    quadA G A (qmul G a b) = (((quadA G A a ^^ quadA G A b) ^^
      dsum (fun s j => a.testBit s && b.testBit j && decide (j < s) && cc G A j s)) ^^
      dsum (fun s j => b.testBit s && a.testBit j && decide (j < s) && cc G A j s)) := by
  unfold quadA
  rw [← dsum_xor, ← dsum_xor, ← dsum_xor]
  refine dsum_congr fun s hs j hj => ?_
  rw [qmul_bit G _ _ hs, qmul_bit G _ _ hj]
  cases a.testBit s <;> cases b.testBit s <;> cases a.testBit j <;> cases b.testBit j <;>
    cases decide (j < s) <;> cases cc G A j s <;> rfl

theorem corr_autApply (G A : Array ℕ) (a b : ℕ) :
    corr G (autApply G A a) (autApply G A b) =
      dsum (fun s t => a.testBit s && b.testBit t && cc G A s t) := by
  rw [corr_eq_bil, bil_congr (fun j hj => autApply_bit G A a hj) (fun t ht => autApply_bit G A b ht),
    bil_sum_left]
  unfold dsum
  refine bx_congr fun s _ => ?_
  rw [bil_sum_right, and_bx]
  refine bx_congr fun t _ => ?_
  simp only [cc, corr_eq_bil]
  cases a.testBit s <;> cases b.testBit t <;> rfl

theorem autApply_mul {G A : Array ℕ} (hA : RelOK G A) (a b : ℕ) :
    autApply G A (qmul G a b) = qmul G (autApply G A a) (autApply G A b) := by
  refine code_ext (autApply_lt _ _ _) (qmul_lt _ _ _) (fun i hi => ?_) ?_
  · rw [autApply_bit G A _ hi, qmul_bit G _ _ hi, autApply_bit G A _ hi, autApply_bit G A _ hi,
      ← bx_xor]
    refine bx_congr fun s hs => ?_
    rw [qmul_bit G _ _ hs]
    cases a.testBit s <;> cases b.testBit s <;> cases (A.getD s 0).testBit i <;> rfl
  · have hL : bx (fun s => (qmul G a b).testBit s && (A.getD s 0).testBit 22) 22 =
        (bx (fun s => a.testBit s && (A.getD s 0).testBit 22) 22 ^^
          bx (fun s => b.testBit s && (A.getD s 0).testBit 22) 22) := by
      rw [← bx_xor]
      refine bx_congr fun s hs => ?_
      rw [qmul_bit G _ _ hs]
      cases a.testBit s <;> cases b.testBit s <;> cases (A.getD s 0).testBit 22 <;> rfl
    rw [autApply_bit22, qmul_bit22, hL, quadA_qmul, qmul_bit22, autApply_bit22, autApply_bit22,
      corr_autApply, ← cross_eq hA]
    ac_rfl

theorem autApply_zero (G A : Array ℕ) : autApply G A 0 = 0 :=
  code_ext (autApply_lt _ _ _) (by decide)
    (fun i hi => by
      rw [autApply_bit G A _ hi, Nat.zero_testBit]
      exact bx_false fun s _ => by rw [Nat.zero_testBit, Bool.false_and])
    (by
      rw [autApply_bit22, Nat.zero_testBit, bx_false fun s _ => by rw [Nat.zero_testBit,
        Bool.false_and], quadA, dsum_false fun s _ t _ => by
          rw [Nat.zero_testBit, Bool.false_and, Bool.false_and, Bool.false_and]]
      rfl)

theorem autApply_x (G A : Array ℕ) : autApply G A (2 ^ 22) = 2 ^ 22 := by
  have hb : ∀ s < 22, (2 ^ 22 : ℕ).testBit s = false := fun s hs =>
    Nat.testBit_two_pow_of_ne (by omega)
  refine code_ext (autApply_lt _ _ _) (by decide) (fun i hi => ?_) ?_
  · rw [autApply_bit G A _ hi, hb i hi]
    exact bx_false fun s hs => by rw [hb s hs, Bool.false_and]
  · rw [autApply_bit22, bx_false fun s hs => by rw [hb s hs, Bool.false_and], quadA,
      dsum_false fun s hs _ _ => by rw [hb s hs, Bool.false_and, Bool.false_and, Bool.false_and]]
    rfl

theorem autApply_two_pow (G A : Array ℕ) {k : ℕ} (hk : k < 22) (hA : A.getD k 0 < 2 ^ 23) :
    autApply G A (2 ^ k) = A.getD k 0 := by
  have hb : ∀ s, (2 ^ k : ℕ).testBit s = decide (k = s) := fun s => Nat.testBit_two_pow
  refine code_ext (autApply_lt _ _ _) hA (fun i hi => ?_) ?_
  · rw [autApply_bit G A _ hi]
    simp only [hb]
    rw [bx_single, decide_eq_true hk, Bool.true_and]
  · rw [autApply_bit22, quadA]
    simp only [hb]
    rw [bx_single, decide_eq_true hk, Bool.true_and,
      dsum_false fun s _ t _ => by
        by_cases h1 : k = s
        · by_cases h2 : k = t
          · subst h1
            subst h2
            simp
          · simp [h2]
        · simp [h1]]
    rw [decide_eq_false (by omega : ¬ k = 22)]
    simp

theorem getD_map_of (A : Array ℕ) (f : ℕ → ℕ) (hf : f 0 = 0) (m : ℕ) :
    (A.map f).getD m 0 = f (A.getD m 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[m]? <;> simp [hf]

theorem autApply_autComp {G B : Array ℕ} (hB : RelOK G B) (A : Array ℕ) (n : ℕ) :
    autApply G (autComp G A B) n = autApply G B (autApply G A n) := by
  have key : ∀ m, autApplyN G (autComp G A B) n m = autApply G B (autApplyN G A n m) := by
    intro m
    induction m with
    | zero =>
      rw [autApplyN, autApplyN]
      split_ifs
      · rw [autApply_x]
      · rw [autApply_zero]
    | succ m ih =>
      rw [autApplyN, autApplyN]
      split_ifs
      · rw [autApply_mul hB, ← ih, autComp, getD_map_of _ _ (autApply_zero G B)]
      · exact ih
  exact key 22

end CertificateChecks.KernelBM.CTIB.CosetQ

end
