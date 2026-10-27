module

public import CFSG.Quasithin.Background.F918U1

public section

set_option exponentiation.threshold 2048

namespace CFSG.Quasithin.D35Chk

attribute [local irreducible] invMask cmTab fxTab fdTab nbTab full bitMasks

private def par (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => (par f n ^^ f n)

private theorem par_zero (f : ℕ → Bool) : par f 0 = false := rfl

private theorem par_succ (f : ℕ → Bool) (n : ℕ) : par f (n + 1) = (par f n ^^ f n) := rfl

private theorem par_succ' (f : ℕ → Bool) (n : ℕ) :
    par f (n + 1) = (f 0 ^^ par (fun k => f (k + 1)) n) := by
  induction n with
  | zero => rw [par_succ, par_zero, par_zero, Bool.false_xor, Bool.xor_false]
  | succ n ih => rw [par_succ, ih, par_succ, Bool.xor_assoc]

private theorem par_congr {f g : ℕ → Bool} {n : ℕ} (h : ∀ k < n, f k = g k) : par f n = par g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [par_succ, par_succ, ih fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)]

private theorem par_xor (f g : ℕ → Bool) (n : ℕ) :
    par (fun k => f k ^^ g k) n = (par f n ^^ par g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [par_succ, ih]
    cases par f n <;> cases par g n <;> cases f n <;> cases g n <;> rfl

private theorem par_false (n : ℕ) : par (fun _ => false) n = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [par_succ, ih, Bool.false_xor]

private theorem testBit_one' (i : ℕ) : (1 : ℕ).testBit i = decide (i = 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.testBit_one_eq_true_iff_self_eq_zero]

private theorem testBit_bit (a k i : ℕ) : (bit a k).testBit i = (decide (i = 0) && a.testBit k) := by
  simp only [bit, Nat.land_eq, Nat.shiftRight_eq', Nat.testBit_and, Nat.testBit_shiftRight, testBit_one']
  by_cases h : i = 0
  · subst h; simp
  · simp [h]

private theorem bit_eq (a k : ℕ) : bit a k = (a.testBit k).toNat := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_bit, Nat.testBit_bool_toNat]

private theorem bit_lt_two (a k : ℕ) : bit a k < 2 := by
  rw [bit_eq]; exact Bool.toNat_lt _

private theorem testBit_bit_mul (a k x i : ℕ) :
    (bit a k * x).testBit i = (a.testBit k && x.testBit i) := by
  rw [bit_eq]; cases a.testBit k <;> simp

private theorem testBit_orFold (g : ℕ → ℕ) (hg : ∀ p, g p < 2) (n c : ℕ) :
    ((List.range n).foldl (fun acc p => Nat.lor acc (Nat.shiftLeft (g p) p)) 0).testBit c =
      (decide (c < n) && (g c).testBit 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.lor_eq, Nat.testBit_or, ih,
      Nat.shiftLeft_eq', Nat.testBit_shiftLeft]
    rcases Nat.lt_trichotomy c n with h | h | h
    · have h1 : ¬ n ≤ c := by omega
      have h2 : c < n + 1 := by omega
      simp [h, h1, h2]
    · subst h; simp
    · have h1 : ¬ c < n := by omega
      have h2 : ¬ c < n + 1 := by omega
      have h3 : (g n).testBit (c - n) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hg n)
          (Nat.pow_le_pow_right (n := 2) (i := 1) (by decide) (by omega)))
      simp [h1, h2, h3]

private def bmk (k : ℕ) : ℕ := (List.range 1024).foldl (fun m b => Nat.lor m (Nat.shiftLeft (bit b k) b)) 0

private theorem testBit_bmk (k c : ℕ) : (bmk k).testBit c = (decide (c < 1024) && c.testBit k) := by
  rw [bmk, testBit_orFold (fun b => bit b k) (fun p => bit_lt_two p k), testBit_bit]
  simp

private theorem bmk_lt (k : ℕ) : bmk k < 2 ^ 1024 := by
  apply Nat.lt_pow_two_of_testBit; intro i hi
  have : ¬ i < 1024 := by omega
  rw [testBit_bmk]; simp [this]

private theorem bitMasks_eq : bitMasks = (List.range 10).map bmk := by
  unfold bitMasks; rfl

private theorem length_bitMasks : bitMasks.length = 10 := by
  rw [bitMasks_eq, List.length_map, List.length_range]

private theorem getD_bitMasks {k : ℕ} (hk : k < 10) : bitMasks.getD k 0 = bmk k := by
  rw [bitMasks_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some]

private theorem testBit_full (c : ℕ) : full.testBit c = decide (c < 1024) := by
  unfold full
  rw [Nat.sub_eq, Nat.pow_eq]
  exact Nat.testBit_two_pow_sub_one 1024 c

private theorem full_lt : full < 2 ^ 1024 := by
  unfold full
  rw [Nat.sub_eq, Nat.pow_eq]
  exact Nat.sub_lt (Nat.two_pow_pos 1024) Nat.one_pos

private theorem testBit_xorSel (ms : List ℕ) (r c : ℕ) :
    (xorSel ms r).testBit c = par (fun k => r.testBit k && (ms.getD k 0).testBit c) ms.length := by
  induction ms generalizing r with
  | nil => rw [xorSel, Nat.zero_testBit]; rfl
  | cons m ms ih =>
    rw [xorSel, Nat.xor_eq, Nat.testBit_xor, ih, List.length_cons, par_succ']
    congr 1
    · have : Nat.land r 1 = bit r 0 := rfl
      rw [this, Nat.mul_eq, testBit_bit_mul, List.getD_cons_zero]
    · apply par_congr; intro k _
      rw [Nat.shiftRight_eq', Nat.testBit_shiftRight, List.getD_cons_succ, Nat.add_comm 1 k]

private theorem testBit_xorSel_bitMasks (r c : ℕ) :
    (xorSel bitMasks r).testBit c = (decide (c < 1024) && par (fun k => r.testBit k && c.testBit k) 10) := by
  rw [testBit_xorSel, length_bitMasks]
  by_cases hc : c < 1024
  · rw [decide_eq_true hc, Bool.true_and]
    apply par_congr; intro k hk
    rw [getD_bitMasks hk, testBit_bmk, decide_eq_true hc, Bool.true_and]
  · rw [decide_eq_false hc, Bool.false_and]
    refine (par_congr fun k hk => ?_).trans (par_false 10)
    rw [getD_bitMasks hk, testBit_bmk, decide_eq_false hc, Bool.false_and, Bool.and_false]

private theorem testBit_kerFold (rows : List ℕ) (acc c : ℕ) :
    (rows.foldl (fun acc r =>
      bif Nat.beq r 0 then acc else Nat.land acc (Nat.xor full (xorSel bitMasks r))) acc).testBit c =
      (acc.testBit c && rows.all fun r => Nat.beq r 0 || (Nat.xor full (xorSel bitMasks r)).testBit c) := by
  induction rows generalizing acc with
  | nil => simp
  | cons r rows ih =>
    rw [List.foldl_cons, ih, List.all_cons]
    cases Nat.beq r 0 <;> simp [Nat.land_eq, Nat.testBit_and, Bool.and_assoc]

private theorem testBit_kerMask (rows : List ℕ) (c : ℕ) :
    (kerMask rows).testBit c = true ↔
      c < 1024 ∧ ∀ r ∈ rows, par (fun k => r.testBit k && c.testBit k) 10 = false := by
  rw [kerMask, testBit_kerFold, testBit_full]
  by_cases hc : c < 1024
  · rw [decide_eq_true hc, Bool.true_and, List.all_eq_true]
    simp only [hc, true_and]
    apply forall₂_congr; intro r _
    rw [Nat.xor_eq, Nat.testBit_xor, testBit_full, testBit_xorSel_bitMasks, decide_eq_true hc, Bool.true_and]
    cases h : Nat.beq r 0
    · simp
    · rw [Nat.eq_of_beq_eq_true h]
      simp [par_false]
  · simp [hc]

private def pRow (col : ℕ → ℕ) (u : ℕ) : ℕ :=
  (List.range 10).foldl (fun acc p => Nat.lor acc (Nat.shiftLeft (bit (col p) u) p)) 0

private theorem packRows_eq (col : ℕ → ℕ) : packRows col = upos.map (pRow col) := rfl

private theorem testBit_pRow (col : ℕ → ℕ) (u k : ℕ) :
    (pRow col u).testBit k = (decide (k < 10) && (col k).testBit u) := by
  rw [pRow, testBit_orFold (fun p => bit (col p) u) (fun p => bit_lt_two _ _), testBit_bit]
  simp

private theorem testBit_colSum (col : ℕ → ℕ) (c u : ℕ) :
    (colSum col c).testBit u = par (fun p => c.testBit p && (col p).testBit u) 10 := by
  have key : ∀ n, ((List.range n).foldl (fun acc p => Nat.xor acc (Nat.mul (bit c p) (col p))) 0).testBit u =
      par (fun p => c.testBit p && (col p).testBit u) n := by
    intro n
    induction n with
    | zero => simp [par_zero]
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.xor_eq, Nat.testBit_xor, ih,
        par_succ, Nat.mul_eq, testBit_bit_mul]
  exact key 10

theorem kerMask_testBit (col : ℕ → ℕ) (c : ℕ) :
    (kerMask (packRows col)).testBit c = true ↔
      c < 1024 ∧ ∀ u ∈ upos, (colSum col c).testBit u = false := by
  rw [testBit_kerMask, packRows_eq]
  simp only [List.forall_mem_map]
  apply and_congr_right; intro _
  apply forall₂_congr; intro u _
  have e : par (fun k => (pRow col u).testBit k && c.testBit k) 10 =
      par (fun p => c.testBit p && (col p).testBit u) 10 :=
    par_congr fun k hk => by rw [testBit_pRow, decide_eq_true hk, Bool.true_and, Bool.and_comm]
  rw [e, testBit_colSum]

theorem colSum_xor (col : ℕ → ℕ) (c d : ℕ) :
    colSum col (Nat.xor c d) = Nat.xor (colSum col c) (colSum col d) := by
  apply Nat.eq_of_testBit_eq; intro u
  simp only [Nat.xor_eq, Nat.testBit_xor, testBit_colSum]
  rw [← par_xor]
  apply par_congr; intro k _
  cases c.testBit k <;> cases d.testBit k <;> simp

theorem colSum_zero (col : ℕ → ℕ) : colSum col 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro u
  rw [testBit_colSum, Nat.zero_testBit]
  exact (par_congr fun k _ => by rw [Nat.zero_testBit, Bool.false_and]).trans (par_false 10)

theorem isSub_kerMask (col : ℕ → ℕ) :
    IsSub (kerMask (packRows col)) ∧ (kerMask (packRows col)).testBit 0 = true := by
  refine ⟨⟨?_, fun c d hc hd => ?_⟩, ?_⟩
  · apply Nat.lt_pow_two_of_testBit; intro i hi
    cases h : (kerMask (packRows col)).testBit i
    · rfl
    · exact absurd ((kerMask_testBit col i).1 h).1 (by omega)
  · rw [kerMask_testBit] at hc hd ⊢
    refine ⟨Nat.xor_lt_two_pow (n := 10) hc.1 hd.1, fun u hu => ?_⟩
    rw [← Nat.xor_eq, colSum_xor, Nat.xor_eq, Nat.testBit_xor, hc.2 u hu, hd.2 u hu]
    rfl
  · rw [kerMask_testBit, colSum_zero]
    exact ⟨by decide, fun u _ => Nat.zero_testBit u⟩

theorem look_lt (T w j : ℕ) : look T w j < 2 ^ w := by
  rw [look, Nat.land_eq, Nat.sub_eq, Nat.pow_eq]
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos)

private theorem packN_acc (f : ℕ → ℕ) (w n acc : ℕ) : packN f w n acc = acc ||| packN f w n 0 := by
  induction n generalizing acc with
  | zero => simp only [packN, Nat.or_zero]
  | succ n ih =>
    simp only [packN]
    rw [ih, ih (Nat.lor 0 _), Nat.lor_eq, Nat.lor_eq, Nat.zero_or, Nat.or_assoc]

private theorem packN_succ_zero (f : ℕ → ℕ) (w n : ℕ) :
    packN f w (n + 1) 0 = f n <<< (w * n) ||| packN f w n 0 := by
  simp only [packN]
  rw [packN_acc f w n (Nat.lor 0 _), Nat.lor_eq, Nat.zero_or, Nat.shiftLeft_eq', Nat.mul_eq]

private theorem packN_lt {f : ℕ → ℕ} {w n : ℕ} (hf : ∀ i < n, f i < 2 ^ w) :
    packN f w n 0 < 2 ^ (w * n) := by
  induction n with
  | zero => simp only [packN]; exact Nat.two_pow_pos _
  | succ n ih =>
    rw [packN_succ_zero]
    apply Nat.or_lt_two_pow
    · rw [Nat.shiftLeft_eq, Nat.mul_add_one, Nat.pow_add, Nat.mul_comm (2 ^ (w * n))]
      exact Nat.mul_lt_mul_of_pos_right (hf n (Nat.lt_succ_self n)) (Nat.two_pow_pos _)
    · exact Nat.lt_of_lt_of_le (ih fun i hi => hf i (Nat.lt_succ_of_lt hi))
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.le_succ n)))

private theorem testBit_packN {f : ℕ → ℕ} {w n j i : ℕ} (hf : ∀ i < n, f i < 2 ^ w) (hj : j < n)
    (hi : i < w) : (packN f w n 0).testBit (w * j + i) = (f j).testBit i := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    rw [packN_succ_zero, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases Nat.lt_or_ge j n with h | h
    · have h1 : ¬ (w * j + i ≥ w * n) := by
        have : w * (j + 1) ≤ w * n := Nat.mul_le_mul_left _ h
        rw [Nat.mul_add_one] at this
        omega
      rw [ih (fun i hi => hf i (Nat.lt_succ_of_lt hi)) h, decide_eq_false h1, Bool.false_and, Bool.false_or]
    · have hjn : j = n := by omega
      rw [hjn]
      have h1 : (packN f w n 0).testBit (w * n + i) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (packN_lt fun i hi => hf i (Nat.lt_succ_of_lt hi))
          (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)))
      rw [h1, Bool.or_false, decide_eq_true (Nat.le_add_right _ _), Bool.true_and, Nat.add_sub_cancel_left]

theorem look_packN {f : ℕ → ℕ} {w n j : ℕ} (hj : j < n) (hf : ∀ i < n, f i < 2 ^ w) :
    look (packN f w n 0) w j = f j := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [look, Nat.land_eq, Nat.shiftRight_eq', Nat.sub_eq, Nat.pow_eq, Nat.mul_eq, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < w
  · rw [testBit_packN hf hj hi, decide_eq_true hi, Bool.and_true]
  · rw [decide_eq_false hi, Bool.and_false, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf j hj)
      (Nat.pow_le_pow_right (by decide) (by omega)))]

private theorem invF_lt (i : ℕ) : (bif isInv i then 1 else 0) < 2 ^ 1 := by
  cases isInv i <;> decide

theorem invMask_lt : invMask < 2 ^ 1024 := by
  have h := packN_lt (f := fun c => bif isInv c then 1 else 0) (w := 1) (n := 1024) fun i _ => invF_lt i
  rw [Nat.one_mul] at h
  unfold invMask
  exact h

theorem testBit_invMask (c : ℕ) : invMask.testBit c = true ↔ c < 1024 ∧ isInv c = true := by
  by_cases hc : c < 1024
  · have h := testBit_packN (f := fun c => bif isInv c then 1 else 0) (w := 1) (n := 1024) (i := 0)
      (fun i _ => invF_lt i) hc Nat.one_pos
    rw [Nat.one_mul, Nat.add_zero] at h
    unfold invMask
    rw [h]
    cases isInv c <;> simp [hc]
  · have h := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le invMask_lt
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hc)))
    rw [h]; simp [hc]

private theorem tabF_lt (g : ℕ → ℕ → ℕ) (i : ℕ) :
    (bif isInv i then kerMask (packRows (g i)) else 0) < 2 ^ 1024 := by
  cases isInv i
  · exact Nat.two_pow_pos 1024
  · exact (isSub_kerMask (g i)).1.1

theorem look_cmTab {c : ℕ} (hc : c < 1024) (hi : isInv c = true) :
    look cmTab 1024 c = kerMask (packRows (commCol c)) := by
  unfold cmTab
  rw [look_packN hc fun i _ => tabF_lt commCol i, hi, Bool.cond_true]

theorem look_fxTab {c : ℕ} (hc : c < 1024) (hi : isInv c = true) :
    look fxTab 1024 c = kerMask (packRows (fixCol c)) := by
  unfold fxTab
  rw [look_packN hc fun i _ => tabF_lt fixCol i, hi, Bool.cond_true]

theorem look_fdTab {c : ℕ} (hc : c < 1024) (hi : isInv c = true) :
    look fdTab 1024 c = kerMask (packRows (fixColD c)) := by
  unfold fdTab
  rw [look_packN hc fun i _ => tabF_lt fixColD i, hi, Bool.cond_true]

theorem testBit_look_nbTab {t : ℕ} (ht : t < 10) (c : ℕ) :
    (look nbTab 1024 t).testBit c = true ↔ c < 1024 ∧ c.testBit t = false := by
  have hf : ∀ i < 10, Nat.xor full (bitMasks.getD i 0) < 2 ^ 1024 := fun i hi => by
    rw [Nat.xor_eq, getD_bitMasks hi]; exact Nat.xor_lt_two_pow full_lt (bmk_lt i)
  unfold nbTab
  rw [look_packN ht hf, Nat.xor_eq, Nat.testBit_xor, testBit_full, getD_bitMasks ht, testBit_bmk]
  by_cases hc : c < 1024 <;> cases c.testBit t <;> simp [hc]

private def tbStep (r s k : ℕ) : ℕ :=
  Nat.add k (bif Nat.beq (Nat.shiftRight r (Nat.add k s)) 0 then 0 else s)

private theorem tbStep_spec {r k : ℕ} (s : ℕ) (hk : 0 < r >>> k) (hs : r >>> (k + 2 * s) = 0) :
    0 < r >>> tbStep r s k ∧ r >>> (tbStep r s k + s) = 0 := by
  unfold tbStep
  cases h : Nat.beq (Nat.shiftRight r (Nat.add k s)) 0
  · have h' := Nat.ne_of_beq_eq_false h
    rw [Nat.shiftRight_eq', Nat.add_eq] at h'
    rw [Bool.cond_false, Nat.add_eq]
    refine ⟨Nat.pos_of_ne_zero h', ?_⟩
    rw [Nat.add_assoc, ← Nat.two_mul]
    exact hs
  · have h' := Nat.eq_of_beq_eq_true h
    rw [Nat.shiftRight_eq', Nat.add_eq] at h'
    rw [Bool.cond_true, Nat.add_eq, Nat.add_zero]
    exact ⟨hk, h'⟩

private theorem topBit_eq_tbStep (r : ℕ) : topBit r = tbStep r 1 (tbStep r 2 (tbStep r 4 (tbStep r 8
    (tbStep r 16 (tbStep r 32 (tbStep r 64 (tbStep r 128 (tbStep r 256
      (bif Nat.beq (Nat.shiftRight r 512) 0 then 0 else 512))))))))) := rfl

theorem topBit_eq_log2 {r : ℕ} (h0 : 0 < r) (h1 : r < 2 ^ 1024) : topBit r = Nat.log2 r := by
  rw [topBit_eq_tbStep]
  have A0 : 0 < r >>> (bif Nat.beq (Nat.shiftRight r 512) 0 then 0 else 512) ∧
      r >>> ((bif Nat.beq (Nat.shiftRight r 512) 0 then 0 else 512) + 2 * 256) = 0 := by
    cases h : Nat.beq (Nat.shiftRight r 512) 0
    · have h' := Nat.ne_of_beq_eq_false h
      rw [Nat.shiftRight_eq'] at h'
      rw [Bool.cond_false]
      exact ⟨Nat.pos_of_ne_zero h', Nat.shiftRight_eq_zero r _ h1⟩
    · have h' := Nat.eq_of_beq_eq_true h
      rw [Nat.shiftRight_eq'] at h'
      rw [Bool.cond_true, Nat.shiftRight_zero, Nat.zero_add]
      exact ⟨h0, h'⟩
  have A1 := tbStep_spec 256 A0.1 A0.2
  have A2 := tbStep_spec 128 A1.1 A1.2
  have A3 := tbStep_spec 64 A2.1 A2.2
  have A4 := tbStep_spec 32 A3.1 A3.2
  have A5 := tbStep_spec 16 A4.1 A4.2
  have A6 := tbStep_spec 8 A5.1 A5.2
  have A7 := tbStep_spec 4 A6.1 A6.2
  have A8 := tbStep_spec 2 A7.1 A7.2
  obtain ⟨B1, B2⟩ := tbStep_spec 1 A8.1 A8.2
  rw [Nat.shiftRight_eq_div_pow] at B1 B2
  refine ((Nat.log2_eq_iff (Nat.pos_iff_ne_zero.1 h0)).2 ⟨(Nat.div_pos_iff.1 B1).2, ?_⟩).symm
  rcases Nat.div_eq_zero_iff.1 B2 with h | h
  · exact absurd h (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
  · exact h

end CFSG.Quasithin.D35Chk
