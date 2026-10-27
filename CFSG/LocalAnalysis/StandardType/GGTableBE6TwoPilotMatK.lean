module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotMat
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotMatKData

public section

namespace CFSG.StandardType.E6TwoMatK

open CFSG.Monster.B.Classical.E6Adjoint CFSG.StandardType.E6TwoMat

@[expose] noncomputable def rowK (a : ℕ) : List ℕ :=
  List.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun x _ ih n => Nat.rec (motive := fun _ => List ℕ) x (fun k _ => ih k) n) tabL a

@[expose] noncomputable def stepK (P : List ℕ) (S : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) S
    (fun c _ acc => Nat.xor acc
      (Nat.shiftLeft (Nat.land (Nat.shiftRight S (Nat.div c 128)) onesK) (Nat.mod c 128))) P

@[expose] noncomputable def simK (w : List ℕ) (S : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) S (fun a _ acc => stepK (rowK a) acc) w

@[expose] noncomputable def wordsAgreeK (w₁ w₂ : List ℕ) : Bool :=
  validWord w₁ && validWord w₂ && Nat.beq (simK w₁ idK) (simK w₂ idK)

@[expose] def laneK (j S : ℕ) : ℕ := (S >>> (78 * j)) % 2 ^ 78

@[expose] def rowOK (P : List ℕ) (a : ℕ) : Bool :=
  ((List.range 78).all fun b =>
    colX a b == (1 <<< b) ^^^ xorMap (fun c => 1 <<< (c % 128)) (P.filter fun c => c / 128 == b)) &&
  P.all fun c => decide (c / 128 < 78) && decide (c % 128 < 78)

@[expose] def onesN : ℕ → ℕ
  | 0 => 0
  | k + 1 => 1 ||| (onesN k <<< 78)

theorem tab_ok : ((List.range 72).all fun i => rowOK (rowK (i + 6)) (i + 6)) = true := by
  decide +kernel

theorem ones_ok : onesK = onesN 78 := by
  decide +kernel

theorem id_ok : ((List.range 78).all fun j => laneK j idK == 1 <<< j) = true := by
  decide +kernel

theorem xorMap_nil (f : ℕ → ℕ) : xorMap f [] = 0 := rfl

theorem xorMap_cons (f : ℕ → ℕ) (l : ℕ) (L : List ℕ) :
    xorMap f (l :: L) = f l ^^^ xorMap f L := rfl

theorem xorMap_append (f : ℕ → ℕ) (L₁ L₂ : List ℕ) :
    xorMap f (L₁ ++ L₂) = xorMap f L₁ ^^^ xorMap f L₂ := by
  induction L₁ with
  | nil => rw [List.nil_append, xorMap_nil, Nat.zero_xor]
  | cons l L ih => rw [List.cons_append, xorMap_cons, xorMap_cons, ih, Nat.xor_assoc]

theorem xorMap_congr {f g : ℕ → ℕ} {L : List ℕ} (h : ∀ l ∈ L, f l = g l) :
    xorMap f L = xorMap g L := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    rw [xorMap_cons, xorMap_cons, h l (by simp), ih fun l' hl => h l' (List.mem_cons_of_mem _ hl)]

theorem xorMap_zero (L : List ℕ) : xorMap (fun _ => 0) L = 0 := by
  induction L with
  | nil => rfl
  | cons l L ih => rw [xorMap_cons, ih, Nat.xor_zero]

theorem xorMap_xor (f g : ℕ → ℕ) (L : List ℕ) :
    xorMap (fun l => f l ^^^ g l) L = xorMap f L ^^^ xorMap g L := by
  induction L with
  | nil => rw [xorMap_nil, xorMap_nil, xorMap_nil, Nat.xor_zero]
  | cons l L ih =>
    rw [xorMap_cons, xorMap_cons, xorMap_cons, ih, Nat.xor_assoc, Nat.xor_assoc,
      ← Nat.xor_assoc (g l), Nat.xor_comm (g l) (xorMap f L), Nat.xor_assoc]

theorem xorMap_single (k x n : ℕ) :
    xorMap (fun b => if b = k then x else 0) (List.range n) = if k < n then x else 0 := by
  induction n with
  | zero => rw [List.range_zero, xorMap_nil, if_neg (Nat.not_lt_zero k)]
  | succ n ih =>
    rw [List.range_succ, xorMap_append, ih, xorMap_cons, xorMap_nil, Nat.xor_zero]
    by_cases h : k < n
    · rw [if_pos h, if_neg (by omega), if_pos (by omega), Nat.xor_zero]
    · by_cases h' : n = k
      · rw [if_neg h, if_pos h', if_pos (by omega), Nat.zero_xor]
      · rw [if_neg h, if_neg h', if_neg (by omega), Nat.xor_zero]

theorem xorMap_bits (m n : ℕ) :
    xorMap (fun b => if m.testBit b then 1 <<< b else 0) (List.range n) = m % 2 ^ n := by
  induction n with
  | zero => rw [List.range_zero, xorMap_nil, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ, xorMap_append, ih, xorMap_cons, xorMap_nil, Nat.xor_zero]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    rcases Nat.lt_trichotomy i n with hi | rfl | hi
    · have : (if m.testBit n then 1 <<< n else 0).testBit i = false := by
        split <;> simp [Nat.one_shiftLeft, Nat.testBit_two_pow] <;> omega
      rw [this, decide_eq_true hi, decide_eq_true (by omega)]
      simp
    · by_cases h : m.testBit i <;> simp [h, Nat.one_shiftLeft, Nat.testBit_two_pow]
    · have : (if m.testBit n then 1 <<< n else 0).testBit i = false := by
        split <;> simp [Nat.one_shiftLeft, Nat.testBit_two_pow] <;> omega
      rw [this, decide_eq_false (by omega), decide_eq_false (by omega)]
      simp

theorem xorMap_filter (t : ℕ → Bool) (g : ℕ → ℕ) (n : ℕ) :
    ∀ P : List ℕ, (∀ c ∈ P, c / 128 < n) →
      xorMap (fun b => if t b then xorMap g (P.filter fun c => c / 128 == b) else 0)
        (List.range n) = xorMap (fun c => if t (c / 128) then g c else 0) P
  | [], _ => by
    simp only [List.filter_nil, xorMap_nil, ite_self, xorMap_zero]
  | c :: P, hP => by
    have e : ∀ b, (if t b then xorMap g ((c :: P).filter fun c => c / 128 == b) else 0) =
        (if b = c / 128 then (if t (c / 128) then g c else 0) else 0) ^^^
          (if t b then xorMap g (P.filter fun c => c / 128 == b) else 0) := by
      intro b
      rw [List.filter_cons]
      by_cases hb : b = c / 128
      · subst hb
        rw [if_pos (beq_self_eq_true _), if_pos rfl, xorMap_cons]
        cases t (c / 128) <;> simp
      · have hcb : (c / 128 == b) = false := beq_eq_false_iff_ne.2 (Ne.symm hb)
        rw [hcb, if_neg hb, Nat.zero_xor]
        rfl
    rw [xorMap_congr (fun b _ => e b), xorMap_xor, xorMap_single,
      xorMap_filter t g n P (fun c' h => hP c' (List.mem_cons_of_mem _ h)), xorMap_cons,
      if_pos (hP c (by simp))]

theorem actX_xor (a x y : ℕ) : actX a (x ^^^ y) = actX a x ^^^ actX a y := by
  unfold actX
  rw [← xorMap_xor]
  refine xorMap_congr fun b _ => ?_
  rw [Nat.testBit_xor]
  cases x.testBit b <;> cases y.testBit b <;> simp

theorem actX_zero (a : ℕ) : actX a 0 = 0 := by
  simp [actX, xorMap_zero]

theorem actX_one (a k : ℕ) : actX a (1 <<< k) = if k < 78 then colX a k else 0 := by
  unfold actX
  rw [← xorMap_single k (colX a k) 78]
  refine xorMap_congr fun b _ => ?_
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : b = k
  · subst h
    simp
  · rw [if_neg h, decide_eq_false (Ne.symm h)]
    rfl

theorem actXF_eq (a f m : ℕ) : actXF a f m = actX a m := by
  induction f generalizing m with
  | zero => rfl
  | succ f ih =>
    by_cases hm : m = 0
    · subst hm
      simp only [actXF, ↓reduceIte]
      exact (actX_zero a).symm
    · simp only [actXF, hm, ↓reduceIte]
      rw [ih, ← actX_one, ← actX_xor]
      congr 1
      rw [Nat.xor_comm m, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

@[expose] def vecP (P : List ℕ) (v : ℕ) : ℕ :=
  v ^^^ xorMap (fun c => if v.testBit (c / 128) then 1 <<< (c % 128) else 0) P

theorem rowOK_iff {P : List ℕ} {a : ℕ} (h : rowOK P a = true) :
    (∀ b < 78, colX a b =
      (1 <<< b) ^^^ xorMap (fun c => 1 <<< (c % 128)) (P.filter fun c => c / 128 == b)) ∧
    ∀ c ∈ P, c / 128 < 78 ∧ c % 128 < 78 := by
  simp only [rowOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at h
  exact h

theorem rowOK_rowK {a : ℕ} (h6 : 6 ≤ a) (h78 : a < 78) : rowOK (rowK a) a = true := by
  have h := tab_ok
  rw [List.all_eq_true] at h
  have := h (a - 6) (List.mem_range.2 (by omega))
  rwa [Nat.sub_add_cancel h6] at this

theorem vecP_eq {P : List ℕ} {a : ℕ} (h : rowOK P a = true) {v : ℕ} (hv : v < 2 ^ 78) :
    vecP P v = actX a v := by
  obtain ⟨hc, hP⟩ := rowOK_iff h
  unfold actX
  rw [xorMap_congr (f := fun b => if v.testBit b then colX a b else 0) (L := List.range 78)
      (g := fun b => (if v.testBit b then 1 <<< b else 0) ^^^
      (if v.testBit b then xorMap (fun c => 1 <<< (c % 128)) (P.filter fun c => c / 128 == b)
        else 0)) (fun b hb => by
      rw [hc b (List.mem_range.1 hb)]
      cases v.testBit b <;> simp),
    xorMap_xor, xorMap_bits, Nat.mod_eq_of_lt hv, xorMap_filter _ _ 78 P fun c h => (hP c h).1]
  rfl

theorem testBit_laneK (j S i : ℕ) :
    (laneK j S).testBit i = (decide (i < 78) && S.testBit (78 * j + i)) := by
  rw [laneK, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem laneK_xor (j x y : ℕ) : laneK j (x ^^^ y) = laneK j x ^^^ laneK j y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_laneK, testBit_laneK, testBit_laneK, Nat.testBit_xor]
  by_cases h : i < 78 <;> simp [h]

theorem laneK_xorMap (j : ℕ) (f : ℕ → ℕ) (L : List ℕ) :
    laneK j (xorMap f L) = xorMap (fun l => laneK j (f l)) L := by
  induction L with
  | nil =>
    rw [xorMap_nil, xorMap_nil]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [testBit_laneK, Nat.zero_testBit, Nat.zero_testBit, Bool.and_false]
  | cons l L ih => rw [xorMap_cons, xorMap_cons, laneK_xor, ih]

theorem testBit_onesN (k p : ℕ) : (onesN k).testBit p = decide (p % 78 = 0 ∧ p / 78 < k) := by
  induction k generalizing p with
  | zero => simp [onesN]
  | succ k ih =>
    have h1 : (1 : ℕ).testBit p = decide (0 = p) := by
      rw [← Nat.testBit_two_pow, Nat.pow_zero]
    rw [onesN, Nat.testBit_or, Nat.testBit_shiftLeft, ih, h1, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

theorem laneK_term {S b r j : ℕ} (hb : b < 78) (hr : r < 78) (hj : j < 78) :
    laneK j (((S >>> b) &&& onesK) <<< r) = if (laneK j S).testBit b then 1 <<< r else 0 := by
  have hlb : (laneK j S).testBit b = S.testBit (78 * j + b) := by
    rw [testBit_laneK, decide_eq_true hb, Bool.true_and]
  rw [hlb, ones_ok]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_laneK, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, testBit_onesN]
  by_cases hi : i = r
  · subst hi
    have hq : 78 * j + i - i = 78 * j := by omega
    have ho : decide ((78 * j) % 78 = 0 ∧ (78 * j) / 78 < 78) = true := by
      rw [decide_eq_true_eq]
      omega
    have hge : decide (78 * j + i ≥ i) = true := by
      rw [decide_eq_true_eq]
      omega
    rw [hq, ho, hge, Nat.add_comm b, decide_eq_true hr, Bool.true_and, Bool.true_and,
      Bool.and_true]
    by_cases hs : S.testBit (78 * j + b)
    · rw [hs, if_pos rfl, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true rfl]
    · rw [Bool.not_eq_true] at hs
      rw [hs, if_neg (by simp), Nat.zero_testBit]
  · have hR : (if S.testBit (78 * j + b) then 1 <<< r else 0).testBit i = false := by
      split
      · rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_false (Ne.symm hi)]
      · exact Nat.zero_testBit i
    rw [hR, Bool.eq_false_iff]
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2, -, h4⟩ := h
    omega

theorem stepK_cons (c : ℕ) (P : List ℕ) (S : ℕ) :
    stepK (c :: P) S = stepK P S ^^^ (((S >>> (c / 128)) &&& onesK) <<< (c % 128)) := rfl

theorem stepK_eq (P : List ℕ) (S : ℕ) :
    stepK P S = S ^^^ xorMap (fun c => ((S >>> (c / 128)) &&& onesK) <<< (c % 128)) P := by
  induction P with
  | nil => rw [xorMap_nil, Nat.xor_zero]; rfl
  | cons c P ih => rw [stepK_cons, ih, xorMap_cons, Nat.xor_assoc, Nat.xor_comm (xorMap _ _)]

theorem laneK_stepK {P : List ℕ} (hP : ∀ c ∈ P, c / 128 < 78 ∧ c % 128 < 78) (S : ℕ) {j : ℕ}
    (hj : j < 78) : laneK j (stepK P S) = vecP P (laneK j S) := by
  rw [stepK_eq, laneK_xor, laneK_xorMap, vecP]
  congr 1
  exact xorMap_congr fun c hc => laneK_term (hP c hc).1 (hP c hc).2 hj

theorem laneK_simK {w : List ℕ} (hw : validWord w = true) (S : ℕ) {j : ℕ} (hj : j < 78) :
    laneK j (simK w S) = actW w (laneK j S) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨⟨h6, h78⟩, hw'⟩ := validWord_cons hw
    change laneK j (stepK (rowK a) (simK w S)) = actXF a 78 (actW w (laneK j S))
    rw [laneK_stepK (rowOK_iff (rowOK_rowK h6 h78)).2 _ hj,
      vecP_eq (v := laneK j (simK w S)) (rowOK_rowK h6 h78) (Nat.mod_lt _ (Nat.two_pow_pos 78)),
      ih hw', actXF_eq]

theorem wordsAgree_of_K {w₁ w₂ : List ℕ} (h : wordsAgreeK w₁ w₂ = true) :
    wordsAgree w₁ w₂ = true := by
  simp only [wordsAgreeK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h₁, h₂⟩, h⟩ := h
  have hid := id_ok
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hid
  simp only [wordsAgree, h₁, h₂, Bool.true_and, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro b hb
  rw [← hid b hb, ← laneK_simK h₁ _ hb, ← laneK_simK h₂ _ hb, h]

end CFSG.StandardType.E6TwoMatK
