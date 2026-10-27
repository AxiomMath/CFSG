module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoRoots
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.StandardType.A6Red.KilledK

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

@[expose] def resK (l : List ℤ) : ℕ × ℕ × ℕ × ℕ :=
  ((l.getD 0 0 % 7).toNat, (l.getD 1 0 % 7).toNat, (l.getD 2 0 % 7).toNat, (l.getD 3 0 % 7).toNat)

@[expose] def RL : List (ℕ × ℕ × ℕ × ℕ) :=
  [(5, 4, 3, 5), (6, 4, 3, 5), (6, 5, 3, 5), (6, 5, 4, 5), (6, 5, 4, 6), (6, 5, 5, 5),
   (6, 5, 5, 6), (6, 5, 5, 0), (6, 6, 5, 5), (6, 6, 5, 6), (6, 6, 5, 0), (6, 6, 6, 6),
   (6, 6, 6, 0), (6, 6, 0, 0), (6, 0, 0, 0), (0, 6, 5, 5), (0, 6, 5, 6), (0, 6, 5, 0),
   (0, 6, 6, 6), (0, 6, 6, 0), (0, 6, 0, 0), (0, 0, 6, 6), (0, 0, 6, 0), (0, 0, 0, 6),
   (0, 0, 0, 1), (0, 0, 1, 0), (0, 0, 1, 1), (0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1),
   (0, 1, 2, 0), (0, 1, 2, 1), (0, 1, 2, 2), (1, 0, 0, 0), (1, 1, 0, 0), (1, 1, 1, 0),
   (1, 1, 1, 1), (1, 1, 2, 0), (1, 1, 2, 1), (1, 1, 2, 2), (1, 2, 2, 0), (1, 2, 2, 1),
   (1, 2, 2, 2), (1, 2, 3, 1), (1, 2, 3, 2), (1, 2, 4, 2), (1, 3, 4, 2), (2, 3, 4, 2)]

theorem RL_eq : rts.map resK = RL := by decide +kernel

noncomputable def valK (e0 e1 e2 e3 : ℕ) (r : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  Prod.rec (motive := fun _ => ℕ) (fun a t => Prod.rec (motive := fun _ => ℕ) (fun b u =>
    Prod.rec (motive := fun _ => ℕ) (fun c d =>
      Nat.mod (Nat.add (Nat.add (Nat.add (Nat.mul e0 a) (Nat.mul e1 b)) (Nat.mul e2 c))
        (Nat.mul e3 d)) 7) u) t) r

noncomputable def cntK (e0 e1 e2 e3 c : ℕ) (L : List (ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun r _ ih =>
      Nat.add (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (valK e0 e1 e2 e3 r) c)) ih) L

theorem valK_lt (e0 e1 e2 e3 : ℕ) (r : ℕ × ℕ × ℕ × ℕ) : valK e0 e1 e2 e3 r < 7 := by
  obtain ⟨a, b, c, d⟩ := r
  exact Nat.mod_lt _ (by norm_num)

theorem cntK_cons (e0 e1 e2 e3 c : ℕ) (r : ℕ × ℕ × ℕ × ℕ) (L : List (ℕ × ℕ × ℕ × ℕ)) :
    cntK e0 e1 e2 e3 c (r :: L) =
      (if valK e0 e1 e2 e3 r = c then 1 else 0) + cntK e0 e1 e2 e3 c L := by
  change Nat.add (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (valK e0 e1 e2 e3 r) c))
    (cntK e0 e1 e2 e3 c L) = _
  cases hb : Nat.beq (valK e0 e1 e2 e3 r) c
  · rw [if_neg (Nat.ne_of_beq_eq_false hb)]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true hb)]
    rfl

theorem sum_rank4 {M : Type*} [AddCommMonoid M] (f : Fin Tag.F4.rank → M) :
    ∑ i, f i = f (idx 0) + f (idx 1) + f (idx 2) + f (idx 3) := by
  have h := Fintype.sum_equiv (finCongr rank_F4) f (fun i : Fin 4 => f ((finCongr rank_F4).symm i))
    (fun i => by simp)
  rw [h, Fin.sum_univ_four]
  rfl

theorem cast_res (x : ℤ) : ((x : ℤ) : ZMod 7) = (((x % 7).toNat : ℕ) : ZMod 7) := by
  have h : (((x % 7).toNat : ℕ) : ℤ) = x % 7 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  rw [← Int.cast_natCast, h]
  exact_mod_cast (ZMod.intCast_mod x 7).symm

theorem val_eq (e : Fin Tag.F4.rank → ZMod 7) (e0 e1 e2 e3 : ℕ) (h0 : e (idx 0) = e0)
    (h1 : e (idx 1) = e1) (h2 : e (idx 2) = e2) (h3 : e (idx 3) = e3) (l : List ℤ) :
    ∑ i, e i * ((vec4 l i : ℤ) : ZMod 7) = ((valK e0 e1 e2 e3 (resK l) : ℕ) : ZMod 7) := by
  rw [sum_rank4, h0, h1, h2, h3]
  change (e0 : ZMod 7) * ((l.getD 0 0 : ℤ) : ZMod 7) + (e1 : ZMod 7) * ((l.getD 1 0 : ℤ) : ZMod 7)
      + (e2 : ZMod 7) * ((l.getD 2 0 : ℤ) : ZMod 7) + (e3 : ZMod 7) * ((l.getD 3 0 : ℤ) : ZMod 7) =
    (((e0 * (l.getD 0 0 % 7).toNat + e1 * (l.getD 1 0 % 7).toNat + e2 * (l.getD 2 0 % 7).toNat
      + e3 * (l.getD 3 0 % 7).toNat) % 7 : ℕ) : ZMod 7)
  rw [ZMod.natCast_mod, cast_res (l.getD 0 0), cast_res (l.getD 1 0), cast_res (l.getD 2 0),
    cast_res (l.getD 3 0)]
  push_cast
  rfl

theorem cnt_eq (e : Fin Tag.F4.rank → ZMod 7) (e0 e1 e2 e3 : ℕ) (h0 : e (idx 0) = e0)
    (h1 : e (idx 1) = e1) (h2 : e (idx 2) = e2) (h3 : e (idx 3) = e3) (c : ZMod 7) :
    (rts.filter (fun l => decide (∑ i, e i * ((vec4 l i : ℤ) : ZMod 7) = c))).length =
      cntK e0 e1 e2 e3 c.val RL := by
  rw [← RL_eq]
  generalize rts = L
  induction L with
  | nil => rfl
  | cons l L ih =>
    rw [List.map_cons, cntK_cons, ← ih, List.filter_cons, val_eq e e0 e1 e2 e3 h0 h1 h2 h3 l]
    have hlt := valK_lt e0 e1 e2 e3 (resK l)
    by_cases h : valK e0 e1 e2 e3 (resK l) = c.val
    · have hd : decide (((valK e0 e1 e2 e3 (resK l) : ℕ) : ZMod 7) = c) = true := by
        rw [decide_eq_true_eq, h, ZMod.natCast_zmod_val]
      rw [if_pos h, if_pos hd, List.length_cons]
      omega
    · have hd : ¬ decide (((valK e0 e1 e2 e3 (resK l) : ℕ) : ZMod 7) = c) = true := by
        rw [decide_eq_true_eq]
        intro h'
        apply h
        rw [← h', ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
      rw [if_neg h, if_neg hd]
      omega

theorem two_val (c : ℕ) : (2 * (c : ZMod 7)).val = 2 * (c % 7) % 7 := by
  rw [ZMod.val_mul, ZMod.val_natCast]
  rfl

noncomputable def okK (e0 e1 e2 e3 : ℕ) : Bool :=
  (e0 == 0 && e1 == 0 && e2 == 0 && e3 == 0) ||
  ((List.range 7).all (fun c =>
      cntK e0 e1 e2 e3 (2 * (c % 7) % 7) RL == cntK e0 e1 e2 e3 (c % 7) RL) == false) ||
  cntK e0 e1 e2 e3 0 RL == 6

noncomputable def allN (f : ℕ → Bool) (k : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun n ih => Bool.rec (motive := fun _ => Bool) false ih (f n)) k

theorem allN_spec (f : ℕ → Bool) : ∀ k, allN f k = true → ∀ n < k, f n = true
  | 0, _, n, hn => absurd hn (Nat.not_lt_zero n)
  | k + 1, h, n, hn => by
    change Bool.rec (motive := fun _ => Bool) false (allN f k) (f k) = true at h
    cases hf : f k
    · rw [hf] at h
      exact (Bool.false_ne_true h).elim
    · rw [hf] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
      · exact allN_spec f k h n hn
      · exact hf

noncomputable def chk (e0 : ℕ) : Bool :=
  allN (fun e1 => allN (fun e2 => allN (fun e3 => okK e0 e1 e2 e3) 7) 7) 7

theorem chk_0 : chk 0 = true := by decide +kernel
theorem chk_1 : chk 1 = true := by decide +kernel
theorem chk_2 : chk 2 = true := by decide +kernel
theorem chk_3 : chk 3 = true := by decide +kernel
theorem chk_4 : chk 4 = true := by decide +kernel
theorem chk_5 : chk 5 = true := by decide +kernel
theorem chk_6 : chk 6 = true := by decide +kernel

theorem ok_all (e0 : ℕ) (h0 : e0 < 7) (e1 : ℕ) (h1 : e1 < 7) (e2 : ℕ) (h2 : e2 < 7) (e3 : ℕ)
    (h3 : e3 < 7) :
    ((e0 == 0 && e1 == 0 && e2 == 0 && e3 == 0) ||
      ((List.range 7).all (fun c =>
        cntK e0 e1 e2 e3 (2 * (c % 7) % 7) RL == cntK e0 e1 e2 e3 (c % 7) RL) == false) ||
      cntK e0 e1 e2 e3 0 RL == 6) = true := by
  have hc : chk e0 = true := by
    interval_cases e0
    exacts [chk_0, chk_1, chk_2, chk_3, chk_4, chk_5, chk_6]
  have h := allN_spec _ 7 (allN_spec _ 7 (allN_spec _ 7 hc e1 h1) e2 h2) e3 h3
  rwa [okK] at h

end CFSG.StandardType.A6Red.KilledK

end
