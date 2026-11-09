module

public import Certificates.Data.CFSGNative.MonsterAxis.Cover

public section

namespace CertificateChecks.KernelAP

open CFSG.Monster.AxisCount.Native CFSG.Monster.AxisCount.Native.Cover
open CFSG.Monster.B.Rep4371.Native (bmaskN wordN popcN permWordN combN umaskN parN packN coeffN)

@[expose] def solveB (b : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc => solveB b k (if b k then acc ^^^ ginvListC.getD k 0 else acc)

@[expose] def quarterBit (T c : Nat) : Bool :=
  (popcN 24 T / 4 + (if T.testBit c then 1 else 0)) % 2 == 1

@[expose] def fbitP (arr : Array Nat) (j k : Nat) : Bool :=
  if j < 12 then
    if k < 12 then popcN 24 (permWordN arr (bmaskN j) &&& bmaskN k) / 2 % 2 == 1
    else quarterBit (permWordN arr (bmaskN j)) (jListC.getD (k - 12) 0)
  else if k < 12 then quarterBit (bmaskN k) arr[jListC.getD (j - 12) 0]!
  else false

@[expose] def fastRowsP (arr : Array Nat) : Array Nat :=
  Array.ofFn (n := 24) fun j => solveB (fbitP arr j.val) 24 0

namespace FastRowsL

theorem solveGo_eq_solveB {w : Nat → Int} {b : Nat → Bool} :
    ∀ {n : Nat}, (∀ k < n, pairBit w k = b k) → ∀ acc, solveGo w n acc = solveB b n acc
  | 0, _, _ => rfl
  | n + 1, h, acc => by
    simp only [solveGo, solveB, h n (Nat.lt_succ_self n)]
    exact solveGo_eq_solveB (fun k hk => h k (Nat.lt_succ_of_lt hk)) _

theorem sumToC_congr {f g : Nat → Int} : ∀ {n : Nat}, (∀ i < n, f i = g i) →
    sumToC f n = sumToC g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sumToC, h n (Nat.lt_succ_self n),
      sumToC_congr (fun i hi => h i (Nat.lt_succ_of_lt hi))]

theorem sumToC_add (f g : Nat → Int) : ∀ n : Nat,
    sumToC (fun i => f i + g i) n = sumToC f n + sumToC g n
  | 0 => rfl
  | n + 1 => by simp only [sumToC, sumToC_add f g n]; omega

theorem sumToC_mul (c : Int) (f : Nat → Int) : ∀ n : Nat,
    sumToC (fun i => c * f i) n = c * sumToC f n
  | 0 => by simp [sumToC]
  | n + 1 => by simp only [sumToC, sumToC_mul c f n, Int.mul_add]

theorem sumToC_succ' (f : Nat → Int) : ∀ n : Nat,
    sumToC f (n + 1) = f 0 + sumToC (fun i => f (i + 1)) n
  | 0 => by simp [sumToC]
  | n + 1 => by
    have := sumToC_succ' f n
    simp only [sumToC] at this ⊢
    omega

theorem sumToC_single (x : Int) {d : Nat} : ∀ {n : Nat}, d < n →
    sumToC (fun i => if i = d then x else 0) n = x
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [sumToC]
    by_cases hd : n = d
    · subst hd
      have : sumToC (fun i => if i = n then x else 0) n = 0 := by
        rw [sumToC_congr (g := fun _ => (0 : Int) * 0) (fun i hi => by
          simp [Nat.ne_of_lt hi])]
        rw [sumToC_mul]
        simp
      simp [this]
    · rw [sumToC_single x (by omega)]
      simp [hd]

theorem sumToC_pop : ∀ (n a : Nat),
    sumToC (fun i => if a.testBit i then 1 else 0) n = (popcN n a : Int)
  | 0, _ => rfl
  | n + 1, a => by
    rw [sumToC_succ']
    have e : (fun i => if a.testBit (i + 1) then (1 : Int) else 0) =
        fun i => if (a / 2).testBit i then 1 else 0 := by
      funext i
      rw [Nat.testBit_div_two]
    rw [e, sumToC_pop n (a / 2)]
    simp only [popcN, Nat.testBit_zero]
    have : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
    rcases this with h | h <;> simp [h] <;> omega

theorem sumToC_const (x : Int) : ∀ n : Nat, sumToC (fun _ => x) n = n * x
  | 0 => by simp [sumToC]
  | n + 1 => by simp only [sumToC, sumToC_const x n]; push_cast; rw [Int.add_mul, Int.one_mul]

theorem sum_and (T S : Nat) :
    sumToC (fun i => (if T.testBit i then 2 else 0) * (if S.testBit i then 2 else 0)) 24 =
      4 * (popcN 24 (T &&& S) : Int) := by
  rw [← sumToC_pop, ← sumToC_mul]
  refine sumToC_congr fun i _ => ?_
  rw [Nat.testBit_and]
  cases T.testBit i <;> cases S.testBit i <;> rfl

theorem sum_quarter (T : Nat) {c : Nat} (hc : c < 24) :
    sumToC (fun i => (if T.testBit i then 2 else 0) * (if i = c then -3 else 1)) 24 =
      2 * (popcN 24 T : Int) + (if T.testBit c then -8 else 0) := by
  rw [← sumToC_pop, ← sumToC_mul, ← sumToC_single (if T.testBit c then -8 else 0) hc,
    ← sumToC_add]
  refine sumToC_congr fun i _ => ?_
  by_cases h : i = c
  · subst h
    cases T.testBit i <;> simp
  · simp only [h, ↓reduceIte]
    cases T.testBit i <;> rfl

theorem sum_two {c d : Nat} (hc : c < 24) (hd : d < 24) :
    sumToC (fun i => (if i = d then (-3 : Int) else 1) * (if i = c then -3 else 1)) 24 =
      16 + (if d = c then 16 else 0) := by
  have e : sumToC (fun i => (if i = d then (-3 : Int) else 1) * (if i = c then -3 else 1)) 24 =
      sumToC (fun _ => (1 : Int)) 24 + sumToC (fun i => if i = d then (-4 : Int) else 0) 24 +
        sumToC (fun i => if i = c then (-4 : Int) else 0) 24 +
        sumToC (fun i => if i = c then (if d = c then (16 : Int) else 0) else 0) 24 := by
    rw [← sumToC_add, ← sumToC_add, ← sumToC_add]
    refine sumToC_congr fun i _ => ?_
    by_cases h1 : i = d <;> by_cases h2 : i = c <;> simp only [h1, h2, ↓reduceIte] <;>
      first | omega | (subst h1; subst h2; simp)
  rw [e, sumToC_const, sumToC_single _ hd, sumToC_single _ hc, sumToC_single _ hc]
  split <;> omega

theorem bit_and (p : Nat) : ((4 * (p : Int)) / 8 % 2 == 1) = (p / 2 % 2 == 1) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  omega

theorem bit_quarter (t : Nat) (b : Bool) :
    ((2 * (t : Int) + (if b then -8 else 0)) / 8 % 2 == 1) =
      ((t / 4 + (if b then 1 else 0)) % 2 == 1) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem bit_two (e : Prop) [Decidable e] :
    ((16 + (if e then (16 : Int) else 0)) / 8 % 2 == 1) = false := by
  split <;> rfl

theorem permValid_inv {arr : Array Nat} (h : permValid arr = true) :
    (∀ i < 24, arr[i]! < 24) ∧ (∀ j < 24, (permInv arr)[j]! < 24) ∧
      (∀ j < 24, arr[(permInv arr)[j]!]! = j) ∧ (∀ i < 24, (permInv arr)[arr[i]!]! = i) := by
  simp only [permValid, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, -⟩ := h
  refine ⟨fun i hi => ?_, fun j hj => ?_, fun j hj => ?_, fun i hi => ?_⟩
  · simpa using List.all_eq_true.1 h1 i (List.mem_range.2 hi)
  · simpa using List.all_eq_true.1 h2 j (List.mem_range.2 hj)
  · simpa using List.all_eq_true.1 h3 j (List.mem_range.2 hj)
  · simpa using List.all_eq_true.1 h4 i (List.mem_range.2 hi)

theorem testBit_combN_pow (p : Nat → Nat) (w i q : Nat)
    (hq : ∀ n < 24, (p n = i ↔ n = q)) : ∀ N ≤ 24,
    (combN (fun n => 2 ^ p n) N w).testBit i = (decide (q < N) && w.testBit q)
  | 0, _ => by simp [combN]
  | N + 1, hN => by
    simp only [combN]
    rw [Nat.testBit_xor, testBit_combN_pow p w i q hq N (by omega)]
    have e := hq N (by omega)
    by_cases hqN : q = N
    · subst hqN
      have : p q = i := e.2 rfl
      cases w.testBit q <;> simp [this]
    · have : p N ≠ i := fun h' => hqN (e.1 h').symm
      have d : decide (q < N + 1) = decide (q < N) := by
        apply decide_eq_decide.2
        omega
      rw [d]
      split <;> simp [this]

theorem testBit_permWordN {arr : Array Nat} (h : permValid arr = true) (S : Nat) {i : Nat}
    (hi : i < 24) : (permWordN arr S).testBit i = S.testBit (permInv arr)[i]! := by
  obtain ⟨-, h2, h3, h4⟩ := permValid_inv h
  unfold permWordN
  rw [testBit_combN_pow (fun n => arr[n]!) S i (permInv arr)[i]!
    (fun n hn => ⟨fun e => by rw [← e, h4 n hn], fun e => by rw [e, h3 i hi]⟩) 24 (Nat.le_refl _)]
  simp [h2 i hi]

theorem permInv_getD {arr : Array Nat} (i : Nat) :
    (permInv arr).toList.getD i 0 = (permInv arr)[i]! := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem jListC_lt (n : Nat) : jListC.getD n 0 < 24 := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp [jListC]

theorem permInv_eq_iff {arr : Array Nat} (h : permValid arr = true) {i c : Nat} (hi : i < 24)
    (hc : c < 24) : (permInv arr)[i]! = c ↔ i = arr[c]! := by
  obtain ⟨-, -, h3, h4⟩ := permValid_inv h
  exact ⟨fun e => by rw [← e, h3 i hi], fun e => by rw [e, h4 c hc]⟩

theorem pairBit_perm {arr : Array Nat} (h : permValid arr = true) (j k : Nat) :
    pairBit (permAct (permInv arr).toList (ellC j)) k = fbitP arr j k := by
  obtain ⟨h1, -, -, -⟩ := permValid_inv h
  unfold pairBit permAct fbitP
  simp only [permInv_getD]
  by_cases hj12 : j < 12
  · have e : ∀ i < 24, ellC j (permInv arr)[i]! =
        if (permWordN arr (bmaskN j)).testBit i then 2 else 0 := fun i hi => by
      simp only [ellC, hj12, ↓reduceIte, testBit_permWordN h _ hi]
    rw [sumToC_congr (g := fun i => (if (permWordN arr (bmaskN j)).testBit i then 2 else 0) *
      ellC k i) fun i hi => by rw [e i hi]]
    simp only [hj12, ↓reduceIte]
    by_cases hk12 : k < 12
    · simp only [ellC, hk12, ↓reduceIte]
      rw [sum_and, bit_and]
    · simp only [ellC, hk12, ↓reduceIte]
      rw [sum_quarter _ (jListC_lt _), bit_quarter]
      rfl
  · have hc := jListC_lt (j - 12)
    have hd := h1 _ hc
    have e : ∀ i < 24, ellC j (permInv arr)[i]! =
        if i = arr[jListC.getD (j - 12) 0]! then -3 else 1 := fun i hi => by
      simp only [ellC, hj12, ↓reduceIte]
      simp only [permInv_eq_iff h hi hc]
    rw [sumToC_congr (g := fun i => (if i = arr[jListC.getD (j - 12) 0]! then -3 else 1) *
      ellC k i) fun i hi => by rw [e i hi]]
    simp only [hj12, ↓reduceIte]
    by_cases hk12 : k < 12
    · simp only [ellC, hk12, ↓reduceIte]
      rw [sumToC_congr (g := fun i => (if (bmaskN k).testBit i then 2 else 0) *
        (if i = arr[jListC.getD (j - 12) 0]! then -3 else 1)) fun i _ => Int.mul_comm _ _,
        sum_quarter _ hd, bit_quarter]
      rfl
    · simp only [ellC, hk12, ↓reduceIte]
      rw [sum_two (jListC_lt _) hd, bit_two]

theorem l2Rows_perm {arr : Array Nat} (h : permValid arr = true) :
    (Gen.perm arr).l2Rows = fastRowsP arr := by
  simp only [Gen.l2Rows, rowsOfAct, fastRowsP, clsCoord]
  congr 1
  funext j
  exact solveGo_eq_solveB (fun k _ => pairBit_perm h j k) 0

end FastRowsL

@[expose] def quarterSum (m T c : Nat) : Int :=
  (2 * (popcN 24 T : Int) + (if T.testBit c then -8 else 0)) -
    2 * (2 * (popcN 24 (T &&& m) : Int) + (if (T &&& m).testBit c then -8 else 0))

@[expose] def twoSum (m c d : Nat) : Int :=
  (16 + (if d = c then 16 else 0)) -
    2 * ((popcN 24 m : Int) + (if m.testBit d then -4 else 0) + (if m.testBit c then -4 else 0) +
      (if m.testBit c then (if d = c then 16 else 0) else 0))

@[expose] def pairSumS (m j k : Nat) : Int :=
  if j < 12 then
    if k < 12 then
      4 * (popcN 24 (bmaskN j &&& bmaskN k) : Int) -
        2 * (4 * (popcN 24 ((bmaskN j &&& m) &&& bmaskN k) : Int))
    else quarterSum m (bmaskN j) (jListC.getD (k - 12) 0)
  else if k < 12 then quarterSum m (bmaskN k) (jListC.getD (j - 12) 0)
  else twoSum m (jListC.getD (k - 12) 0) (jListC.getD (j - 12) 0)

@[expose] def fastRowsS (a : Nat) : Array Nat :=
  Array.ofFn (n := 24) fun j => solveB (fun k => pairSumS (wordN a) j.val k / 8 % 2 == 1) 24 0

namespace FastRowsL

theorem sumToC_sign (m : Nat) (f : Nat → Int) (n : Nat) :
    sumToC (fun i => if m.testBit i then -f i else f i) n =
      sumToC f n - 2 * sumToC (fun i => if m.testBit i then f i else 0) n := by
  rw [sumToC_congr (g := fun i => f i + (-2) * (if m.testBit i then f i else 0)) (fun i _ => by
    cases m.testBit i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega), sumToC_add,
    sumToC_mul]
  omega

theorem sum_and_m (m T S : Nat) :
    sumToC (fun i => if m.testBit i then
      (if T.testBit i then (2 : Int) else 0) * (if S.testBit i then 2 else 0) else 0) 24 =
      4 * (popcN 24 ((T &&& m) &&& S) : Int) := by
  rw [← sum_and]
  refine sumToC_congr fun i _ => ?_
  rw [Nat.testBit_and]
  cases m.testBit i <;> cases T.testBit i <;> simp

theorem sum_quarter_m (m T : Nat) {c : Nat} (hc : c < 24) :
    sumToC (fun i => if m.testBit i then
      (if T.testBit i then (2 : Int) else 0) * (if i = c then -3 else 1) else 0) 24 =
      2 * (popcN 24 (T &&& m) : Int) + (if (T &&& m).testBit c then -8 else 0) := by
  rw [← sum_quarter _ hc]
  refine sumToC_congr fun i _ => ?_
  rw [Nat.testBit_and]
  cases m.testBit i <;> cases T.testBit i <;> simp

theorem sum_quarter' (T : Nat) {c : Nat} (hc : c < 24) :
    sumToC (fun i => (if i = c then (-3 : Int) else 1) * (if T.testBit i then 2 else 0)) 24 =
      2 * (popcN 24 T : Int) + (if T.testBit c then -8 else 0) := by
  rw [← sum_quarter T hc]
  exact sumToC_congr fun i _ => Int.mul_comm _ _

theorem sum_quarter_m' (m T : Nat) {c : Nat} (hc : c < 24) :
    sumToC (fun i => if m.testBit i then
      (if i = c then (-3 : Int) else 1) * (if T.testBit i then 2 else 0) else 0) 24 =
      2 * (popcN 24 (T &&& m) : Int) + (if (T &&& m).testBit c then -8 else 0) := by
  rw [← sum_quarter_m m T hc]
  refine sumToC_congr fun i _ => ?_
  split
  · exact Int.mul_comm _ _
  · rfl

theorem sum_two_m (m : Nat) {c d : Nat} (hc : c < 24) (hd : d < 24) :
    sumToC (fun i => if m.testBit i then
      (if i = d then (-3 : Int) else 1) * (if i = c then -3 else 1) else 0) 24 =
      (popcN 24 m : Int) + (if m.testBit d then -4 else 0) + (if m.testBit c then -4 else 0) +
        (if m.testBit c then (if d = c then 16 else 0) else 0) := by
  rw [← sumToC_pop, ← sumToC_single (if m.testBit d then (-4 : Int) else 0) hd,
    ← sumToC_single (if m.testBit c then (-4 : Int) else 0) hc,
    ← sumToC_single (if m.testBit c then (if d = c then (16 : Int) else 0) else 0) hc,
    ← sumToC_add, ← sumToC_add, ← sumToC_add]
  refine sumToC_congr fun i _ => ?_
  by_cases h1 : i = d <;> by_cases h2 : i = c
  · subst h1
    subst h2
    cases m.testBit i <;> simp
  · subst h1
    cases m.testBit i <;> simp [h2]
  · subst h2
    cases m.testBit i <;> simp [h1, Ne.symm h1]
  · cases m.testBit i <;> simp [h1, h2]

theorem pairSum_sign (m j k : Nat) :
    sumToC (fun i => signAct m (ellC j) i * ellC k i) 24 = pairSumS m j k := by
  unfold signAct
  rw [sumToC_congr
    (g := fun i => if m.testBit i then -(ellC j i * ellC k i) else ellC j i * ellC k i)
    (fun i _ => by cases m.testBit i <;> simp [Int.neg_mul]), sumToC_sign]
  unfold pairSumS
  by_cases hj12 : j < 12 <;> by_cases hk12 : k < 12 <;>
    simp only [ellC, hj12, hk12, ↓reduceIte]
  · rw [sum_and, sum_and_m]
  · rw [sum_quarter _ (jListC_lt _), sum_quarter_m _ _ (jListC_lt _)]
    rfl
  · rw [sum_quarter' _ (jListC_lt _), sum_quarter_m' _ _ (jListC_lt _)]
    rfl
  · rw [sum_two (jListC_lt _) (jListC_lt _), sum_two_m _ (jListC_lt _) (jListC_lt _)]
    rfl

theorem l2Rows_sign (a : Nat) : (Gen.sign a).l2Rows = fastRowsS a := by
  simp only [Gen.l2Rows, rowsOfAct, fastRowsS, clsCoord]
  congr 1
  funext j
  refine solveGo_eq_solveB (fun k _ => ?_) 0
  unfold pairBit
  rw [pairSum_sign]

end FastRowsL

@[expose] def xorFold (s y : Nat) : Nat := y ^^^ (y >>> s)

@[expose] def parFold32 (x : Nat) : Bool :=
  xorFold 1 (xorFold 2 (xorFold 4 (xorFold 8 (xorFold 16 x)))) % 2 == 1

@[expose] def coeffFold (w : Nat) : Nat := packN (fun k => parFold32 (w &&& umaskN k)) 12

@[expose] def permValidF (arr : Array Nat) : Bool :=
  arr.size == 24 && (List.range 24).all (fun i => arr[i]! < 24) &&
  (List.range 24).all (fun j => (permInv arr)[j]! < 24) &&
  (List.range 24).all (fun j => arr[(permInv arr)[j]!]! == j) &&
  (List.range 24).all (fun i => (permInv arr)[arr[i]!]! == i) &&
  (List.range 12).all fun i =>
    wordN (coeffFold (permWordN arr (bmaskN i))) == permWordN arr (bmaskN i) &&
    wordN (coeffFold (permWordN (permInv arr) (bmaskN i))) == permWordN (permInv arr) (bmaskN i)

namespace ParFoldL

theorem popcN_add_shift : ∀ (n m x : Nat), popcN (n + m) x = popcN n x + popcN m (x >>> n)
  | 0, m, x => by simp [popcN]
  | n + 1, m, x => by
    have e : x >>> (n + 1) = (x / 2) >>> n := by
      simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    rw [Nat.add_right_comm, popcN, popcN, popcN_add_shift n m (x / 2), e, Nat.add_assoc]

theorem popcN_zero : ∀ n, popcN n 0 = 0
  | 0 => rfl
  | n + 1 => by simp [popcN, popcN_zero n]

theorem xor_mod_two (a b : Nat) : (a ^^^ b) % 2 = (a % 2 + b % 2) % 2 := by
  have h := Nat.testBit_xor a b 0
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one (a ^^^ b) with hx | hx <;> simp_all

theorem popcN_xor : ∀ (n a b : Nat), popcN n (a ^^^ b) % 2 = (popcN n a + popcN n b) % 2
  | 0, _, _ => rfl
  | n + 1, a, b => by
    simp only [popcN]
    rw [Nat.xor_div_two, Nat.add_mod, popcN_xor n (a / 2) (b / 2), xor_mod_two]
    omega

theorem popcN_fold (s x : Nat) : popcN (s + s) x % 2 = popcN s (xorFold s x) % 2 := by
  rw [xorFold, popcN_xor, popcN_add_shift]

theorem parFold32_eq {x : Nat} (hx : x < 2 ^ 24) : parFold32 x = parN 24 x := by
  have h32 : popcN 32 x = popcN 24 x := by
    rw [popcN_add_shift 24 8, Nat.shiftRight_eq_zero x 24 hx, popcN_zero, Nat.add_zero]
  have e : popcN 24 x % 2 = xorFold 1 (xorFold 2 (xorFold 4 (xorFold 8 (xorFold 16 x)))) % 2 := by
    rw [← h32, popcN_fold 16, popcN_fold 8, popcN_fold 4, popcN_fold 2, popcN_fold 1]
    simp [popcN]
  simp only [parFold32, parN, e]

theorem umaskN_lt (k : Nat) : umaskN k < 2 ^ 24 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [umaskN]

theorem coeffFold_eq : coeffFold = coeffN := by
  funext w
  have e : (fun k => parFold32 (w &&& umaskN k)) = fun k => parN 24 (w &&& umaskN k) :=
    funext fun k => parFold32_eq (Nat.and_lt_two_pow w (umaskN_lt k))
  unfold coeffFold coeffN
  rw [e]

theorem permValidF_eq : permValidF = permValid := by
  funext arr
  unfold permValidF permValid
  rw [coeffFold_eq]

theorem isVis_perm {arr : Array Nat} (h : permValidF arr = true) : (Gen.perm arr).isVis = true := by
  rw [permValidF_eq] at h
  exact h

end ParFoldL

@[expose] def swar8 (b : Nat) : Nat :=
  let v := b - ((b >>> 1) &&& 0x55)
  let v := (v &&& 0x33) + ((v >>> 2) &&& 0x33)
  (v + (v >>> 4)) &&& 0x0f

@[expose] def popcB (x : Nat) : Nat :=
  swar8 (x &&& 255) + swar8 ((x >>> 8) &&& 255) + swar8 ((x >>> 16) &&& 255)

@[expose] def quarterBitB (T c : Nat) : Bool :=
  (popcB T / 4 + (if T.testBit c then 1 else 0)) % 2 == 1

@[expose] def fbitPB (arr : Array Nat) (j k : Nat) : Bool :=
  if j < 12 then
    if k < 12 then popcB (permWordN arr (bmaskN j) &&& bmaskN k) / 2 % 2 == 1
    else quarterBitB (permWordN arr (bmaskN j)) (jListC.getD (k - 12) 0)
  else if k < 12 then quarterBitB (bmaskN k) arr[jListC.getD (j - 12) 0]!
  else false

@[expose] def fastRowsPB (arr : Array Nat) : Array Nat :=
  Array.ofFn (n := 24) fun j => solveB (fbitPB arr j.val) 24 0

@[expose] def quarterSumB (m T c : Nat) : Int :=
  (2 * (popcB T : Int) + (if T.testBit c then -8 else 0)) -
    2 * (2 * (popcB (T &&& m) : Int) + (if (T &&& m).testBit c then -8 else 0))

@[expose] def twoSumB (m c d : Nat) : Int :=
  (16 + (if d = c then 16 else 0)) -
    2 * ((popcB m : Int) + (if m.testBit d then -4 else 0) + (if m.testBit c then -4 else 0) +
      (if m.testBit c then (if d = c then 16 else 0) else 0))

@[expose] def pairSumSB (m j k : Nat) : Int :=
  if j < 12 then
    if k < 12 then
      4 * (popcB (bmaskN j &&& bmaskN k) : Int) -
        2 * (4 * (popcB ((bmaskN j &&& m) &&& bmaskN k) : Int))
    else quarterSumB m (bmaskN j) (jListC.getD (k - 12) 0)
  else if k < 12 then quarterSumB m (bmaskN k) (jListC.getD (j - 12) 0)
  else twoSumB m (jListC.getD (k - 12) 0) (jListC.getD (j - 12) 0)

@[expose] def fastRowsSB (a : Nat) : Array Nat :=
  Array.ofFn (n := 24) fun j => solveB (fun k => pairSumSB (wordN a) j.val k / 8 % 2 == 1) 24 0

namespace PopcBL

theorem swar8_eq : ∀ b < 256, swar8 b = popcN 8 b := by decide +kernel

theorem popcN_mod : ∀ (n x : Nat), popcN n (x % 2 ^ n) = popcN n x
  | 0, _ => rfl
  | n + 1, x => by
    have h1 : x % 2 ^ (n + 1) % 2 = x % 2 :=
      Nat.mod_mod_of_dvd x (Nat.dvd_of_mod_eq_zero (by simp [Nat.pow_succ, Nat.mul_mod_left]))
    have h2 : x % 2 ^ (n + 1) / 2 = x / 2 % 2 ^ n := by
      rw [Nat.pow_succ', Nat.mod_mul_right_div_self]
    simp only [popcN, h1, h2, popcN_mod n (x / 2)]

theorem swar8_and (y : Nat) : swar8 (y &&& 255) = popcN 8 y := by
  have e : y &&& 255 = y % 2 ^ 8 := Nat.and_two_pow_sub_one_eq_mod y 8
  rw [swar8_eq _ (by rw [e]; exact Nat.mod_lt _ (by decide)), e, popcN_mod]

theorem popcB_eq (x : Nat) : popcB x = popcN 24 x := by
  rw [popcB, swar8_and, swar8_and, swar8_and, ParFoldL.popcN_add_shift 8 16,
    ParFoldL.popcN_add_shift 8 8, ← Nat.shiftRight_add, Nat.add_assoc]

theorem popcB_fun : popcB = popcN 24 := funext popcB_eq

theorem fastRowsPB_eq : fastRowsPB = fastRowsP := by
  funext arr
  unfold fastRowsPB fastRowsP fbitPB fbitP quarterBitB quarterBit
  rw [popcB_fun]

theorem fastRowsSB_eq : fastRowsSB = fastRowsS := by
  funext a
  unfold fastRowsSB fastRowsS pairSumSB pairSumS quarterSumB quarterSum twoSumB twoSum
  rw [popcB_fun]

end PopcBL

end CertificateChecks.KernelAP

end
