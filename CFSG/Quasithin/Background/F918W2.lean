module

public import CFSG.Quasithin.Background.F918W1

public section

namespace CFSG.Quasithin.D35ValChk

open scoped Matrix

private theorem testBit_eq_mod (a k : Nat) : a.testBit k = decide ((a >>> k) % 2 = 1) := by
  rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]

private theorem bit_eq_ite (a k : Nat) : bit a k = if a.testBit k then 1 else 0 := by
  simp only [bit, Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod, testBit_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one (a >>> k) with h | h <;> simp [h]

private theorem bit_le_one (a k : Nat) : bit a k ≤ 1 := by
  rw [bit_eq_ite]; split <;> decide

private theorem testBit_bit_mul (r k x m : Nat) :
    (bit r k * x).testBit m = (r.testBit k && x.testBit m) := by
  rw [bit_eq_ite]; cases r.testBit k <;> simp

private theorem testBit_lor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

private theorem testBit_rowOf (a i j : Nat) :
    (rowOf a i).testBit j = (a.testBit (6 * i + j) && decide (j < 6)) := by
  simp only [rowOf, Nat.land_eq, Nat.shiftRight_eq', Nat.mul_eq, Nat.testBit_and, Nat.testBit_shiftRight]
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.testBit_two_pow_sub_one]

private theorem testBit_vecMul (r b j : Nat) : (vecMul r b).testBit j =
    ((((((r.testBit 0 && (rowOf b 0).testBit j) ^^ (r.testBit 1 && (rowOf b 1).testBit j)) ^^
      (r.testBit 2 && (rowOf b 2).testBit j)) ^^ (r.testBit 3 && (rowOf b 3).testBit j)) ^^
      (r.testBit 4 && (rowOf b 4).testBit j)) ^^ (r.testBit 5 && (rowOf b 5).testBit j)) := by
  simp only [vecMul, Nat.xor_eq, Nat.mul_eq, Nat.testBit_xor, testBit_bit_mul]

private theorem testBit_bmul (a b : Nat) {i j : Nat} (hi : i < 6) (hj : j < 6) :
    (bmul a b).testBit (6 * i + j) =
      ((((((a.testBit (6 * i + 0) && b.testBit (6 * 0 + j)) ^^
        (a.testBit (6 * i + 1) && b.testBit (6 * 1 + j))) ^^
        (a.testBit (6 * i + 2) && b.testBit (6 * 2 + j))) ^^
        (a.testBit (6 * i + 3) && b.testBit (6 * 3 + j))) ^^
        (a.testBit (6 * i + 4) && b.testBit (6 * 4 + j))) ^^
        (a.testBit (6 * i + 5) && b.testBit (6 * 5 + j))) := by
  rcases i with _ | _ | _ | _ | _ | _ | i <;> rcases j with _ | _ | _ | _ | _ | _ | j <;> (try omega) <;>
    simp [-Nat.testBit_zero, bmul, testBit_vecMul, testBit_rowOf]

private theorem ite_xor_zmod (x y : Bool) :
    (if (x ^^ y) = true then (1 : ZMod 2) else 0) =
      (if x = true then 1 else 0) + (if y = true then 1 else 0) := by
  cases x <;> cases y <;> decide

private theorem ite_and_zmod (x y : Bool) :
    (if (x && y) = true then (1 : ZMod 2) else 0) =
      (if x = true then 1 else 0) * (if y = true then 1 else 0) := by
  cases x <;> cases y <;> decide

theorem toM_bmul (a b : Nat) : toM (bmul a b) = toM a * toM b := by
  ext i j
  simp only [toM, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_six]
  rw [testBit_bmul a b i.2 j.2, ite_xor_zmod, ite_xor_zmod, ite_xor_zmod, ite_xor_zmod, ite_xor_zmod,
    ite_and_zmod, ite_and_zmod, ite_and_zmod, ite_and_zmod, ite_and_zmod, ite_and_zmod]
  rfl

private theorem testBit_idm {i j : Nat} (hi : i < 6) (hj : j < 6) :
    idm.testBit (6 * i + j) = decide (i = j) := by
  have key : ∀ i < 6, ∀ j < 6, idm.testBit (6 * i + j) = decide (i = j) := by decide
  exact key i hi j hj

theorem toM_idm : toM idm = 1 := by
  ext i j
  simp only [toM, Matrix.of_apply, testBit_idm i.2 j.2, Matrix.one_apply, decide_eq_true_eq, Fin.val_inj]

theorem toM_inj {a b : Nat} (ha : a < 2 ^ 36) (hb : b < 2 ^ 36) (h : toM a = toM b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rcases Nat.lt_or_ge k 36 with hk | hk
  · have e := congrFun (congrFun h ⟨k / 6, by omega⟩) ⟨k % 6, by omega⟩
    simp only [toM, Matrix.of_apply, Nat.div_add_mod] at e
    revert e
    cases a.testBit k <;> cases b.testBit k <;> decide
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hk)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hk))]

private theorem lor_lt {x y N : Nat} (hx : x < 2 ^ N) (hy : y < 2 ^ N) : Nat.lor x y < 2 ^ N :=
  Nat.or_lt_two_pow hx hy

private theorem xor_lt {x y N : Nat} (hx : x < 2 ^ N) (hy : y < 2 ^ N) : Nat.xor x y < 2 ^ N :=
  Nat.xor_lt_two_pow hx hy

private theorem shiftLeft_lt {x n s N : Nat} (hx : x < 2 ^ n) (h : n + s ≤ N) :
    Nat.shiftLeft x s < 2 ^ N := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  calc x * 2 ^ s < 2 ^ n * 2 ^ s := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos s)
    _ = 2 ^ (n + s) := (Nat.pow_add 2 n s).symm
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by decide) h

private theorem bit_mul_le (c p x : Nat) : Nat.mul (bit c p) x ≤ x := by
  have := Nat.mul_le_mul_right x (bit_le_one c p)
  rwa [Nat.one_mul] at this

private theorem rowOf_lt (a i : Nat) : rowOf a i < 2 ^ 6 := by
  unfold rowOf
  simp only [Nat.land_eq]
  exact Nat.and_lt_two_pow _ (by decide)

private theorem vecMul_lt (r b : Nat) : vecMul r b < 2 ^ 6 := by
  have h : ∀ k, Nat.mul (bit r k) (rowOf b k) < 2 ^ 6 := fun k =>
    Nat.lt_of_le_of_lt (bit_mul_le r k _) (rowOf_lt b k)
  exact xor_lt (xor_lt (xor_lt (xor_lt (xor_lt (h 0) (h 1)) (h 2)) (h 3)) (h 4)) (h 5)

theorem bmul_lt (a b : Nat) : bmul a b < 2 ^ 36 := by
  have h := fun i => vecMul_lt (rowOf a i) b
  exact lor_lt (lor_lt (lor_lt (lor_lt (lor_lt
    (Nat.lt_of_lt_of_le (h 0) (Nat.pow_le_pow_right (by decide) (by decide)))
    (shiftLeft_lt (h 1) (by decide))) (shiftLeft_lt (h 2) (by decide)))
    (shiftLeft_lt (h 3) (by decide))) (shiftLeft_lt (h 4) (by decide))) (shiftLeft_lt (h 5) (by decide))

private theorem kent_lt (a p : Nat) : kent a p < 4 := by
  have : kent a p < 2 ^ 2 := by
    unfold kent
    simp only [Nat.land_eq]
    exact Nat.and_lt_two_pow _ (by decide)
  simpa using this

private theorem smul_lt_four : ∀ e < 4, ∀ f < 4, smul e f < 4 := by decide

private def pat (e : Nat) : Nat := Nat.land (Nat.shiftRight blkTab (Nat.mul 8 e)) 255

private theorem pat_lt (e : Nat) : pat e < 2 ^ 8 := by
  unfold pat
  simp only [Nat.land_eq]
  exact Nat.and_lt_two_pow _ (by decide)

theorem expand_lt (c : Nat) : expand c < 2 ^ 36 := by
  have h : ∀ e, pat e < 2 ^ 8 := pat_lt
  unfold expand
  exact lor_lt (lor_lt (lor_lt (lor_lt (lor_lt (lor_lt (lor_lt (lor_lt
    (Nat.lt_of_lt_of_le (h (kent c 0)) (Nat.pow_le_pow_right (by decide) (by decide)))
    (shiftLeft_lt (h (kent c 2)) (by decide))) (shiftLeft_lt (h (kent c 4)) (by decide)))
    (shiftLeft_lt (h (kent c 6)) (by decide)))
    (shiftLeft_lt (h (kent c 8)) (by decide))) (shiftLeft_lt (h (kent c 10)) (by decide)))
    (shiftLeft_lt (h (kent c 12)) (by decide)))
    (shiftLeft_lt (h (kent c 14)) (by decide))) (shiftLeft_lt (h (kent c 16)) (by decide))

private theorem lt_pow_of_lt {x a b : Nat} (hx : x < 2 ^ a) (h : a ≤ b) : x < 2 ^ b :=
  Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 2 > 0) h)

private theorem smul_lt64 (e v : Nat) : smul e v < 2 ^ 6 := by
  unfold smul
  simp only [Nat.land_eq]
  exact Nat.and_lt_two_pow _ (by decide)

private theorem krowMul_lt (a s b : Nat) : krowMul a s b < 2 ^ 6 := by
  unfold krowMul
  exact xor_lt (xor_lt (smul_lt64 _ _) (smul_lt64 _ _)) (smul_lt64 _ _)

theorem kmul_lt (a b : Nat) : kmul a b < 2 ^ 18 := by
  unfold kmul
  exact lor_lt (lor_lt (lt_pow_of_lt (krowMul_lt a 0 b) (by decide))
    (shiftLeft_lt (krowMul_lt a 6 b) (by decide))) (shiftLeft_lt (krowMul_lt a 12 b) (by decide))

private theorem fmul_lt2 (e f : Nat) (he : e < 4) (hf : f < 4) : fmul e f < 2 ^ 2 := by
  have := smul_lt_four e he f hf
  simpa [fmul] using this

theorem kapply_lt (c v : Nat) : kapply c v < 2 ^ 6 := by
  have h : ∀ p q, fmul (kent c p) (kent v q) < 2 ^ 2 := fun p q => fmul_lt2 _ _ (kent_lt c p) (kent_lt v q)
  unfold kapply
  exact lor_lt (lor_lt
    (lt_pow_of_lt (xor_lt (xor_lt (h _ _) (h _ _)) (h _ _)) (by decide))
    (shiftLeft_lt (xor_lt (xor_lt (h _ _) (h _ _)) (h _ _)) (by decide)))
    (shiftLeft_lt (xor_lt (xor_lt (h _ _) (h _ _)) (h _ _)) (by decide))

theorem vecOfBits_inj {v w : Nat} (hv : v < 64) (hw : w < 64) (h : vecOfBits v = vecOfBits w) : v = w := by
  apply Nat.eq_of_testBit_eq
  intro k
  rcases Nat.lt_or_ge k 6 with hk | hk
  · have e := congrFun h ⟨k, hk⟩
    simp only [vecOfBits] at e
    revert e
    cases v.testBit k <;> cases w.testBit k <;> decide
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide : 2 > 0) hk)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide : 2 > 0) hk))]

theorem vecOfBits_surj (x : Fin 6 → ZMod 2) : ∃ v, v < 64 ∧ vecOfBits v = x := by
  revert x
  decide +kernel

theorem vecOfBits_xor (v w : Nat) : vecOfBits (Nat.xor v w) = vecOfBits v + vecOfBits w := by
  ext i
  simp only [vecOfBits, Nat.xor_eq, Nat.testBit_xor, Pi.add_apply, ite_xor_zmod]

private theorem bitSet_eq (s e : Nat) : bitSet s e = s.testBit e := by
  have h : bitSet s e = Nat.beq (bit s e) 1 := rfl
  rw [h, bit_eq_ite]
  cases s.testBit e <;> rfl

theorem bitSet_land (m n v : Nat) : bitSet (Nat.land m n) v = (bitSet m v && bitSet n v) := by
  simp only [bitSet_eq, Nat.land_eq, Nat.testBit_and]

private theorem testBit_shiftLeft_one (n k : Nat) : (Nat.shiftLeft 1 n).testBit k = decide (n = k) := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

private theorem fixMask_foldl (c : Nat) (n init k : Nat) :
    ((List.range n).foldl
      (fun m v => if Nat.beq (kapply c v) v then Nat.lor m (Nat.shiftLeft 1 v) else m) init).testBit k =
      (init.testBit k || (decide (k < n) && Nat.beq (kapply c k) k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split
    · rename_i hc
      rw [testBit_lor, ih, testBit_shiftLeft_one]
      by_cases hk : k = n
      · subst hk; simp [hc]
      · have h1 : decide (n = k) = false := by simp [Ne.symm hk]
        have h2 : decide (k < n + 1) = decide (k < n) := by
          apply Bool.eq_iff_iff.mpr; simp; omega
        rw [h1, h2]; simp
    · rename_i hc
      rw [ih]
      by_cases hk : k = n
      · subst hk; simp at hc; simp [hc]
      · have h2 : decide (k < n + 1) = decide (k < n) := by
          apply Bool.eq_iff_iff.mpr; simp; omega
        rw [h2]

theorem bitSet_fixMask (c v : Nat) (hv : v < 64) : bitSet (fixMask c) v = true ↔ kapply c v = v := by
  rw [bitSet_eq]
  unfold fixMask
  rw [fixMask_foldl]
  simp [hv]

theorem popc_eq_card (m : Nat) :
    popc m = ((Finset.range 64).filter fun v => bitSet m v = true).card := by
  have key : ∀ n init, (List.range n).foldl (fun c i => Nat.add c (bit m i)) init =
      init + ((Finset.range n).filter fun v => bitSet m v = true).card := by
    intro n
    induction n with
    | zero => intro init; simp
    | succ n ih =>
      intro init
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, Finset.range_add_one,
        Finset.filter_insert]
      have hb : bit m n = if bitSet m n = true then 1 else 0 := by
        rw [bitSet_eq, bit_eq_ite]
      by_cases h : bitSet m n = true
      · simp only [h, ↓reduceIte, Finset.card_insert_of_notMem
          (by simp : n ∉ Finset.filter (fun v => bitSet m v = true) (Finset.range n))]
        rw [hb]; simp [h, Nat.add_assoc]
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [hb]; simp [h]
  unfold popc
  rw [key]
  simp

private theorem pat_testBit_of_ne (e t : Nat) (h0 : t ≠ 0) (h1 : t ≠ 1) (h6 : t ≠ 6) (h7 : t ≠ 7) :
    (pat e).testBit t = false := by
  rcases Nat.lt_or_ge e 4 with he | he
  · have key : ∀ e < 4, ∀ t < 8, t = 0 ∨ t = 1 ∨ t = 6 ∨ t = 7 ∨ (pat e).testBit t = false := by decide
    rcases Nat.lt_or_ge t 8 with ht | ht
    · rcases key e he t ht with h | h | h | h | h
      · exact absurd h h0
      · exact absurd h h1
      · exact absurd h h6
      · exact absurd h h7
      · exact h
    · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (pat_lt e) (Nat.pow_le_pow_right (by decide : 2 > 0) ht))
  · have : pat e = 0 := by
      unfold pat blkTab
      simp only [Nat.land_eq, Nat.shiftRight_eq', Nat.mul_eq]
      rw [Nat.shiftRight_eq_zero _ _ (by
        calc 1136820480 < 2 ^ 32 := by decide
          _ ≤ 2 ^ (8 * e) := Nat.pow_le_pow_right (by decide : 2 > 0) (by omega))]
      simp
    rw [this]; simp

private theorem expand_eq (c : Nat) : expand c = Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor
    (Nat.lor (pat (kent c 0)) (Nat.shiftLeft (pat (kent c 2)) 2)) (Nat.shiftLeft (pat (kent c 4)) 4))
    (Nat.shiftLeft (pat (kent c 6)) 12)) (Nat.shiftLeft (pat (kent c 8)) 14))
    (Nat.shiftLeft (pat (kent c 10)) 16)) (Nat.shiftLeft (pat (kent c 12)) 24))
    (Nat.shiftLeft (pat (kent c 14)) 26)) (Nat.shiftLeft (pat (kent c 16)) 28) := rfl

private theorem testBit_expand (c m : Nat) (hm : m < 36) :
    (expand c).testBit m =
      (pat (kent c (6 * (m / 12) + 2 * ((m % 6) / 2)))).testBit (6 * ((m / 6) % 2) + m % 2) := by
  rw [expand_eq]
  simp only [testBit_lor, Nat.shiftLeft_eq', Nat.testBit_shiftLeft]
  interval_cases m <;> simp [pat_testBit_of_ne]

private theorem testBit_kent (a p t : Nat) (ht : t < 2) : (kent a p).testBit t = a.testBit (p + t) := by
  unfold kent
  simp only [Nat.land_eq, Nat.shiftRight_eq', Nat.testBit_and, Nat.testBit_shiftRight]
  rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  simp [ht]

private theorem entry_of_pat : ∀ e < 4, ∀ e' < 4, (pat e).testBit 0 = (pat e').testBit 0 →
    (pat e).testBit 1 = (pat e').testBit 1 → e = e' := by decide

private theorem kent_eq_of_expand_eq {a b : Nat} (h : expand a = expand b) {i j : Nat} (hi : i < 3) (hj : j < 3) :
    kent a (6 * i + 2 * j) = kent b (6 * i + 2 * j) := by
  have h0 := congrArg (fun x => x.testBit (12 * i + 2 * j)) h
  have h1 := congrArg (fun x => x.testBit (12 * i + 2 * j + 1)) h
  rw [testBit_expand a _ (by omega), testBit_expand b _ (by omega)] at h0 h1
  have e1 : 6 * ((12 * i + 2 * j) / 12) + 2 * (((12 * i + 2 * j) % 6) / 2) = 6 * i + 2 * j := by omega
  have e2 : 6 * ((12 * i + 2 * j + 1) / 12) + 2 * (((12 * i + 2 * j + 1) % 6) / 2) = 6 * i + 2 * j := by omega
  have e3 : 6 * (((12 * i + 2 * j) / 6) % 2) + (12 * i + 2 * j) % 2 = 0 := by omega
  have e4 : 6 * (((12 * i + 2 * j + 1) / 6) % 2) + (12 * i + 2 * j + 1) % 2 = 1 := by omega
  rw [e1, e3] at h0
  rw [e2, e4] at h1
  exact entry_of_pat _ (kent_lt a _) _ (kent_lt b _) h0 h1

theorem expand_inj {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) (h : expand a = expand b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rcases Nat.lt_or_ge k 18 with hk | hk
  · have hkk : kent a (2 * (k / 2)) = kent b (2 * (k / 2)) := by
      have := kent_eq_of_expand_eq h (i := (k / 2) / 3) (j := (k / 2) % 3) (by omega) (by omega)
      rw [show 6 * ((k / 2) / 3) + 2 * ((k / 2) % 3) = 2 * (k / 2) by omega] at this
      exact this
    have ta := testBit_kent a (2 * (k / 2)) (k % 2) (by omega)
    have tb := testBit_kent b (2 * (k / 2)) (k % 2) (by omega)
    rw [show 2 * (k / 2) + k % 2 = k by omega] at ta tb
    rw [← ta, ← tb, hkk]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 2 > 0) hk)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 2 > 0) hk))]

private def rowK (e0 e1 e2 f0 f1 f2 : Nat) : Nat :=
  Nat.xor (Nat.xor (fmul e0 f0) (fmul e1 f1)) (fmul e2 f2)

private theorem rowK_lt (e0 e1 e2 f0 f1 f2 : Nat) (h0 : e0 < 4) (h1 : e1 < 4) (h2 : e2 < 4) (g0 : f0 < 4)
    (g1 : f1 < 4) (g2 : f2 < 4) : rowK e0 e1 e2 f0 f1 f2 < 2 ^ 2 :=
  xor_lt (xor_lt (fmul_lt2 _ _ h0 g0) (fmul_lt2 _ _ h1 g1)) (fmul_lt2 _ _ h2 g2)

private theorem rowK_testBit_high (e0 e1 e2 f0 f1 f2 q : Nat) (h0 : e0 < 4) (h1 : e1 < 4) (h2 : e2 < 4)
    (g0 : f0 < 4) (g1 : f1 < 4) (g2 : f2 < 4) (hq : 2 ≤ q) : (rowK e0 e1 e2 f0 f1 f2).testBit q = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (rowK_lt e0 e1 e2 f0 f1 f2 h0 h1 h2 g0 g1 g2)
    (Nat.pow_le_pow_right (by decide : 2 > 0) hq))

private theorem kapply_eq (c v : Nat) : kapply c v = Nat.lor (Nat.lor
    (rowK (kent c 0) (kent c 2) (kent c 4) (kent v 0) (kent v 2) (kent v 4))
    (Nat.shiftLeft (rowK (kent c 6) (kent c 8) (kent c 10) (kent v 0) (kent v 2) (kent v 4)) 2))
    (Nat.shiftLeft (rowK (kent c 12) (kent c 14) (kent c 16) (kent v 0) (kent v 2) (kent v 4)) 4) := rfl

private theorem testBit_kapply (c v i a : Nat) (hi : i < 3) (ha : a < 2) :
    (kapply c v).testBit (2 * i + a) =
      (rowK (kent c (6 * i)) (kent c (6 * i + 2)) (kent c (6 * i + 4)) (kent v 0) (kent v 2) (kent v 4)).testBit a := by
  rw [kapply_eq]
  simp only [testBit_lor, Nat.shiftLeft_eq', Nat.testBit_shiftLeft]
  interval_cases i <;> interval_cases a <;> simp [kent_lt, rowK_testBit_high]

private theorem key_entry : ∀ e < 4, ∀ f < 4, ∀ a < 2,
    (fmul e f).testBit a =
      (((pat e).testBit (6 * a) && f.testBit 0) ^^ ((pat e).testBit (6 * a + 1) && f.testBit 1)) := by
  decide

private theorem key_row (e0 e1 e2 f0 f1 f2 a : Nat) (h0 : e0 < 4) (h1 : e1 < 4) (h2 : e2 < 4) (g0 : f0 < 4)
    (g1 : f1 < 4) (g2 : f2 < 4) (ha : a < 2) :
    (rowK e0 e1 e2 f0 f1 f2).testBit a =
      (((((pat e0).testBit (6 * a) && f0.testBit 0) ^^ ((pat e0).testBit (6 * a + 1) && f0.testBit 1)) ^^
        (((pat e1).testBit (6 * a) && f1.testBit 0) ^^ ((pat e1).testBit (6 * a + 1) && f1.testBit 1))) ^^
        (((pat e2).testBit (6 * a) && f2.testBit 0) ^^ ((pat e2).testBit (6 * a + 1) && f2.testBit 1))) := by
  simp only [rowK, Nat.xor_eq, Nat.testBit_xor, key_entry e0 h0 f0 g0 a ha, key_entry e1 h1 f1 g1 a ha,
    key_entry e2 h2 f2 g2 a ha]

private theorem testBit_expand_row (c i a j : Nat) (hi : i < 3) (ha : a < 2) (_hj : j < 6) :
    (expand c).testBit (6 * (2 * i + a) + j) = (pat (kent c (6 * i + 2 * (j / 2)))).testBit (6 * a + j % 2) := by
  rw [testBit_expand c _ (by omega)]
  have e1 : 6 * ((6 * (2 * i + a) + j) / 12) + 2 * (((6 * (2 * i + a) + j) % 6) / 2) = 6 * i + 2 * (j / 2) := by omega
  have e2 : 6 * (((6 * (2 * i + a) + j) / 6) % 2) + (6 * (2 * i + a) + j) % 2 = 6 * a + j % 2 := by omega
  rw [e1, e2]

private theorem testBit_vec (v j : Nat) (_hj : j < 6) : v.testBit j = (kent v (2 * (j / 2))).testBit (j % 2) := by
  rw [testBit_kent v _ _ (by omega)]
  congr 1
  omega

theorem toM_expand_mulVec (c v : Nat) : toM (expand c) *ᵥ vecOfBits v = vecOfBits (kapply c v) := by
  ext ⟨k, hk⟩
  obtain ⟨i, a, hi, ha, rfl⟩ : ∃ i a, i < 3 ∧ a < 2 ∧ k = 2 * i + a := ⟨k / 2, k % 2, by omega, by omega, by omega⟩
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, toM, Matrix.of_apply, vecOfBits, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.add_zero, Nat.reduceMod]
  have T0 := testBit_expand_row c i a 0 hi ha (by decide)
  have T1 := testBit_expand_row c i a 1 hi ha (by decide)
  have T2 := testBit_expand_row c i a 2 hi ha (by decide)
  have T3 := testBit_expand_row c i a 3 hi ha (by decide)
  have T4 := testBit_expand_row c i a 4 hi ha (by decide)
  have T5 := testBit_expand_row c i a 5 hi ha (by decide)
  have V0 := testBit_vec v 0 (by decide)
  have V1 := testBit_vec v 1 (by decide)
  have V2 := testBit_vec v 2 (by decide)
  have V3 := testBit_vec v 3 (by decide)
  have V4 := testBit_vec v 4 (by decide)
  have V5 := testBit_vec v 5 (by decide)
  simp only [Nat.add_zero, Nat.reduceDiv, Nat.reduceMod, Nat.mul_zero, Nat.reduceMul] at T0 T1 T2 T3 T4 T5
  simp only [Nat.reduceDiv, Nat.reduceMod, Nat.mul_zero, Nat.reduceMul] at V0 V1 V2 V3 V4 V5
  simp only [T0, T1, T2, T3, T4, T5, V0, V1, V2, V3, V4, V5, testBit_kapply c v i a hi ha,
    key_row _ _ _ _ _ _ a (kent_lt c _) (kent_lt c _) (kent_lt c _) (kent_lt v _) (kent_lt v _) (kent_lt v _) ha,
    ite_xor_zmod, ite_and_zmod]
  ring

end CFSG.Quasithin.D35ValChk
