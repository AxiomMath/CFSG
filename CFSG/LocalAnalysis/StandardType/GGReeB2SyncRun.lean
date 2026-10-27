module

public import CFSG.LocalAnalysis.StandardType.GGReeB2StepThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGReeB2SigmaOrder
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Push
import Mathlib.Algebra.Ring.Fin
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

open Fin.NatCast

public section

namespace CFSG.StandardType.ReeB2Fixed

private def tyB (b bn α β : Bool) : Bool :=
  let u := xor β bn
  if b then !u else (α && !u)

private def stepB (a b bn : Bool) (s : Bool × Bool × Bool) : Bool × Bool × Bool :=
  let u := xor s.2.1 bn
  let c : Bool := match a, b with
    | false, false => s.1 && s.2.2
    | false, true => s.1 || s.2.2
    | true, false => s.1 && u
    | true, true => u
  (s.2.1, c, a && tyB b bn s.1 s.2.1)

private def digB (a b : Bool) (s : Bool × Bool × Bool) : Bool := xor (xor b s.2.2) (xor s.1 a)

private def own (a t : Bool) : ℤ := if a then (if t then -1 else 1) else 0

private theorem stepB_arith : ∀ a b bn α β π : Bool, (a = true → π = false) →
    (b.toNat : ℤ) + π.toNat + own a (stepB a b bn (α, β, π)).2.2 + α.toNat
      = (digB a b (α, β, π)).toNat + 2 * (stepB a b bn (α, β, π)).2.1.toNat := by
  decide

private theorem stepB_pending : ∀ a b bn α β π : Bool,
    (stepB a b bn (α, β, π)).2.2 = true → a = true ∧ β = bn := by
  decide

private theorem stepB_slot_type : ∀ a b bn α β π : Bool, a = true → π = false →
    (stepB a b bn (α, β, π)).2.2 = true → digB false bn (stepB a b bn (α, β, π)) = true := by
  decide

private theorem stepB_slot_untyped : ∀ b bn α β π : Bool, π = false →
    (stepB true b bn (α, β, π)).2.2 = false →
      (digB true b (α, β, π) = true ∨ digB false bn (stepB true b bn (α, β, π)) = true) := by
  decide

private theorem stepB_sync : ∀ (a₀ b₀ a1 b2 : Bool) (s s' : Bool × Bool × Bool),
    stepB a1 a1 b2 (stepB false false a1 (stepB a₀ b₀ false s)) =
      stepB a1 a1 b2 (stepB false false a1 (stepB a₀ b₀ false s')) := by
  intro a₀ b₀ a1 b2 s s'
  obtain ⟨α, β, π⟩ := s
  obtain ⟨α', β', π'⟩ := s'
  revert a₀ b₀ a1 b2 α β π α' β' π'
  decide

private theorem tyB_eq_pstar (e : ℕ) (A B : Finset (Fin e)) (q : Fin e) (α β : Bool) :
    pstar e A B q α β = tyB (decide (q ∈ B)) (decide (succσ e q ∈ B)) α β := by
  by_cases hq : q ∈ B <;> by_cases hs : succσ e q ∈ B <;>
    simp [pstar, tyB, hq, hs]


private def runFrom {S : Type} {e : ℕ} [NeZero e] (F : Fin e → S → S) (j : Fin e) (s : S) : ℕ → S
  | 0 => s
  | n + 1 => F (j + (n : Fin e)) (runFrom F j s n)

private theorem fin_add_one_val (e n : ℕ) [NeZero e] (hn : n < e) :
    ((n : Fin e) + 1).val = (n + 1) % e := by
  rcases e with _ | _ | m
  · exact absurd rfl (NeZero.ne 0)
  · have hn0 : n = 0 := by omega
    subst hn0
    simp
  · rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt hn, Fin.val_one',
      Nat.mod_eq_of_lt (by omega : 1 < m + 2)]

private theorem runFrom_add {S : Type} {e : ℕ} [NeZero e] (F : Fin e → S → S) (j : Fin e) (s : S)
    (m n : ℕ) :
    runFrom F j s (m + n) = runFrom F (j + (m : Fin e)) (runFrom F j s m) n := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
      rw [Nat.add_succ]
      simp only [runFrom]
      rw [ih]
      congr 1
      rw [Nat.cast_add, add_assoc]

private theorem exists_run_of_const {S : Type} {e : ℕ} [NeZero e] (F : Fin e → S → S) (j : Fin e)
    (hconst : ∀ s s' : S, runFrom F j s e = runFrom F j s' e) (s₀ : S) :
    ∃ x : Fin e → S, ∀ k, x (k + 1) = F k (x k) := by
  let y : S := runFrom F j s₀ e
  have hy : runFrom F j y e = y := hconst y s₀
  refine ⟨fun k => runFrom F j y (k - j).val, ?_⟩
  intro k
  change runFrom F j y (k + 1 - j).val = F k (runFrom F j y (k - j).val)
  set n : ℕ := (k - j).val with hn
  have hnlt : n < e := by rw [hn]; exact (k - j).isLt
  have hkn : k = j + (n : Fin e) := by
    have hcast : (n : Fin e) = k - j := by
      apply Fin.ext
      rw [Fin.val_natCast, Nat.mod_eq_of_lt hnlt, hn]
    rw [hcast, add_sub_cancel]
  have hvalaux : ((n : Fin e) + 1).val = (n + 1) % e := fin_add_one_val e n hnlt
  have hval : (k + 1 - j).val = (n + 1) % e := by
    have hkj : k + 1 - j = (n : Fin e) + 1 := by
      rw [hkn, add_assoc, add_sub_cancel_left]
    rw [hkj, hvalaux]
  by_cases hlt : n + 1 < e
  · rw [hval, Nat.mod_eq_of_lt hlt]
    change F (j + (n : Fin e)) (runFrom F j y n) = F k (runFrom F j y n)
    rw [← hkn]
  · have hne : n + 1 = e := by omega
    rw [hval, hne, Nat.mod_self]
    change y = F k (runFrom F j y n)
    have hstep : F k (runFrom F j y n) = runFrom F j y e := by
      rw [hkn]
      change runFrom F j y (n + 1) = runFrom F j y e
      rw [hne]
    rw [hstep, hy]

private theorem fin_natCast_add (e a b : ℕ) [NeZero e] :
    ((a : Fin e) + (b : Fin e)) = ((a + b : ℕ) : Fin e) := by
  ext
  simp only [Fin.val_add, Fin.val_natCast]
  exact (Nat.add_mod a b e).symm

private theorem two_add_neg_three (e : ℕ) [NeZero e] : (2 : Fin e) + -3 = -1 := by
  have h3 : (3 : Fin e) = 2 + 1 := by norm_num
  rw [h3, neg_add]
  abel

private theorem neg_one_add_two (e : ℕ) [NeZero e] : (-1 : Fin e) + 2 = 1 := by
  have h2 : (2 : Fin e) = 1 + 1 := by norm_num
  rw [h2, ← add_assoc, neg_add_cancel, zero_add]

private theorem cast_e_sub_three (e : ℕ) [NeZero e] (h3 : 3 ≤ e) :
    ((e - 3 : ℕ) : Fin e) = -3 := by
  have hsum : ((e - 3 : ℕ) : Fin e) + ((3 : ℕ) : Fin e) = 0 := by
    rw [fin_natCast_add, show (e - 3) + 3 = e by omega, Fin.natCast_self]
  have hneg : (-3 : Fin e) + ((3 : ℕ) : Fin e) = 0 := by
    rw [show ((3 : ℕ) : Fin e) = (3 : Fin e) from rfl]
    exact neg_add_cancel 3
  exact add_right_cancel (hsum.trans hneg.symm)

private theorem run_const {e : ℕ} [NeZero e] (h3 : 3 ≤ e) (a b : Fin e → Bool) (k₀ : Fin e)
    (hk0a : a k₀ = false) (hk0b : b k₀ = false) (hk1 : a (k₀ + 1) = b (k₀ + 1))
    (s s' : Bool × Bool × Bool) :
    runFrom (fun k => stepB (a k) (b k) (b (k + 1))) (k₀ + 2) s e =
      runFrom (fun k => stepB (a k) (b k) (b (k + 1))) (k₀ + 2) s' e := by
  let F : Fin e → Bool × Bool × Bool → Bool × Bool × Bool :=
    fun k => stepB (a k) (b k) (b (k + 1))
  have he3 : (e - 3) + 3 = e := by omega
  have h3unfold : ∀ (j' : Fin e) (t : Bool × Bool × Bool),
      runFrom F j' t 3 = F (j' + 2) (F (j' + 1) (F (j' + 0) t)) := fun j' t => rfl
  let j' : Fin e := (k₀ + 2) + ((e - 3 : ℕ) : Fin e)
  have hp2 : j' + 2 = k₀ + 1 := by
    simp only [j']
    rw [cast_e_sub_three e h3]
    calc (k₀ + 2) + -3 + 2 = k₀ + ((2 + -3) + 2) := by abel
      _ = k₀ + (-1 + 2) := by rw [two_add_neg_three]
      _ = k₀ + 1 := by rw [neg_one_add_two]
  have hp1 : j' + 1 = k₀ := by
    simp only [j']
    rw [cast_e_sub_three e h3]
    calc (k₀ + 2) + -3 + 1 = k₀ + ((2 + -3) + 1) := by abel
      _ = k₀ + (-1 + 1) := by rw [two_add_neg_three]
      _ = k₀ := by rw [neg_add_cancel, add_zero]
  have hp0 : j' + 0 = k₀ - 1 := by
    simp only [j']
    rw [cast_e_sub_three e h3]
    calc (k₀ + 2) + -3 + 0 = k₀ + (2 + -3) := by abel
      _ = k₀ + -1 := by rw [two_add_neg_three]
      _ = k₀ - 1 := (sub_eq_add_neg k₀ 1).symm
  have hcomp : ∀ t : Bool × Bool × Bool,
      runFrom F (k₀ + 2) t e =
        F (j' + 2) (F (j' + 1) (F (j' + 0) (runFrom F (k₀ + 2) t (e - 3)))) := by
    intro t
    rw [← congrArg (fun m => runFrom F (k₀ + 2) t m) he3,
        runFrom_add F (k₀ + 2) t (e - 3) 3]
    exact h3unfold j' (runFrom F (k₀ + 2) t (e - 3))
  have hF0 : ∀ t : Bool × Bool × Bool,
      F (j' + 0) t = stepB (a (k₀ - 1)) (b (k₀ - 1)) false t := by
    intro t
    rw [hp0]
    show stepB (a (k₀ - 1)) (b (k₀ - 1)) (b ((k₀ - 1) + 1)) t = _
    rw [sub_add_cancel, hk0b]
  have hF1 : ∀ t : Bool × Bool × Bool,
      F (j' + 1) t = stepB false false (a (k₀ + 1)) t := by
    intro t
    rw [hp1]
    show stepB (a k₀) (b k₀) (b (k₀ + 1)) t = _
    rw [hk0a, hk0b, ← hk1]
  have hF2 : ∀ t : Bool × Bool × Bool,
      F (j' + 2) t = stepB (a (k₀ + 1)) (a (k₀ + 1)) (b ((k₀ + 1) + 1)) t := by
    intro t
    rw [hp2]
    show stepB (a (k₀ + 1)) (b (k₀ + 1)) (b ((k₀ + 1) + 1)) t = _
    rw [← hk1]
  have key : ∀ t : Bool × Bool × Bool,
      runFrom F (k₀ + 2) t e =
        stepB (a (k₀ + 1)) (a (k₀ + 1)) (b ((k₀ + 1) + 1))
          (stepB false false (a (k₀ + 1))
            (stepB (a (k₀ - 1)) (b (k₀ - 1)) false (runFrom F (k₀ + 2) t (e - 3)))) := by
    intro t
    rw [hcomp t, hF0, hF1, hF2]
  rw [key s, key s']
  exact stepB_sync (a (k₀ - 1)) (b (k₀ - 1)) (a (k₀ + 1)) (b ((k₀ + 1) + 1)) _ _

private def la (e : ℕ) [NeZero e] (A : Finset (Fin e)) (k : Fin e) : Bool := decide (sig e k ∈ A)

private theorem exists_run (e : ℕ) (he : Odd e) (h3 : 3 ≤ e) [NeZero e] (A B : Finset (Fin e))
    (p : Fin e) (hp : SyncAt e A B p) :
    ∃ x : Fin e → Bool × Bool × Bool, ∀ k : Fin e,
      x (k + 1) = stepB (la e A k) (la e B k) (la e B (k + 1)) (x k) := by
  obtain ⟨k₀, hk0⟩ := (sig_bijective e he).2 p
  have hpA : p ∉ A := hp.1
  have hpB : p ∉ B := hp.2.1
  have hiff : succσ e p ∈ A ↔ succσ e p ∈ B := hp.2.2
  have hk0A : la e A k₀ = false := by
    simp only [la]
    rw [hk0]
    exact decide_eq_false_iff_not.mpr hpA
  have hk0B : la e B k₀ = false := by
    simp only [la]
    rw [hk0]
    exact decide_eq_false_iff_not.mpr hpB
  have hk1 : la e A (k₀ + 1) = la e B (k₀ + 1) := by
    simp only [la]
    rw [sig_add_one e he k₀, hk0]
    by_cases h : succσ e p ∈ A
    · have h' : succσ e p ∈ B := hiff.mp h
      rw [decide_eq_true h, decide_eq_true h']
    · have h' : succσ e p ∉ B := fun hb => h (hiff.mpr hb)
      rw [decide_eq_false_iff_not.mpr h, decide_eq_false_iff_not.mpr h']
  have hconst := run_const h3 (la e A) (la e B) k₀ hk0A hk0B hk1
  exact exists_run_of_const (fun k => stepB (la e A k) (la e B k) (la e B (k + 1)))
    (k₀ + 2) hconst (false, false, false)

private theorem la_indep (e : ℕ) (he : Odd e) [NeZero e] (A : Finset (Fin e)) (hI : IndepSigma e A)
    (k : Fin e) (hk : la e A k = true) : la e A (k + 1) = false := by
  unfold la at hk ⊢
  rw [decide_eq_false_iff_not]
  intro h
  apply hI (sig e k) (of_decide_eq_true hk)
  rw [← sig_add_one e he k]
  exact h

private theorem run_valid (e : ℕ) (he : Odd e) [NeZero e] (A B : Finset (Fin e)) (hI : IndepSigma e A)
    (x : Fin e → Bool × Bool × Bool)
    (hx : ∀ k : Fin e, x (k + 1) = stepB (la e A k) (la e B k) (la e B (k + 1)) (x k))
    (k : Fin e) (hk : la e A k = true) : (x k).2.2 = false := by
  by_contra h
  have hπ : (x k).2.2 = true := by
    cases hx2 : (x k).2.2
    · exact absurd hx2 h
    · rfl
  have hkm1 : k - 1 + 1 = k := sub_add_cancel k 1
  have hxk : x k =
      stepB (la e A (k - 1)) (la e B (k - 1)) (la e B (k - 1 + 1)) (x (k - 1)) := by
    conv_lhs => rw [← hkm1]
    exact hx (k - 1)
  have hpend := stepB_pending (la e A (k - 1)) (la e B (k - 1))
    (la e B (k - 1 + 1)) (x (k - 1)).1 (x (k - 1)).2.1 (x (k - 1)).2.2
  have hthis : (stepB (la e A (k - 1)) (la e B (k - 1))
      (la e B (k - 1 + 1)) (x (k - 1))).2.2 = true := by
    rw [← hxk]
    exact hπ
  obtain ⟨ha, -⟩ := hpend hthis
  have hk' : la e A ((k - 1) + 1) = false := la_indep e he A hI (k - 1) ha
  rw [hkm1, hk] at hk'
  exact Bool.noConfusion hk'


private theorem sum_pos_eq_sum_idx (e : ℕ) (he : Odd e) [NeZero e] {M : Type} [AddCommMonoid M]
    (A : Finset (Fin e)) (f : Fin e → M) :
    ∑ q ∈ A, f q = ∑ k : Fin e, if sig e k ∈ A then f (sig e k) else 0 := by
  let σe : Fin e ≃ Fin e := Equiv.ofBijective (sig e) (sig_bijective e he)
  have h1 : ∑ k : Fin e, (if sig e k ∈ A then f (sig e k) else 0) =
      ∑ q : Fin e, if q ∈ A then f q else 0 := by
    simpa [σe] using Equiv.sum_comp σe (fun q => if q ∈ A then f q else 0)
  have h2 : ∑ q ∈ A, f q = ∑ q : Fin e, if q ∈ A then f q else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [h2, ← h1]

private theorem r_pow_succ (e : ℕ) (he : Odd e) [NeZero e] (k : Fin e) :
    r e ^ ((k + 1 : Fin e) : ℕ) = r e ^ (k : ℕ) * r e := by
  have hmod : ((k + 1 : Fin e) : ℕ) ≡ (k : ℕ) + 1 [MOD e] := by
    rw [Fin.val_add]
    exact (Nat.mod_modEq ((k : ℕ) + ((1 : Fin e) : ℕ)) e).trans
      (Nat.ModEq.add (Nat.ModEq.refl _)
        (by rw [Fin.val_one']; exact Nat.mod_modEq 1 e))
  rw [pow_eq_pow_of_modEq hmod (r_pow_self e he), pow_succ]

private theorem term_eq (e : ℕ) (he : Odd e) [NeZero e] (t : Bool) (k : Fin e) :
    term e t (sig e k) =
      if t then r e ^ ((k + 1 : Fin e) : ℕ) - r e ^ (k : ℕ) else r e ^ (k : ℕ) := by
  unfold term
  cases t with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact (r_pow_eq e he k).symm
  | true =>
      simp only [if_true]
      rw [show R e = r e - 1 from rfl, ← r_pow_eq e he k, r_pow_succ e he k]
      ring

private theorem S_eq_sum_idx (e : ℕ) (he : Odd e) [NeZero e] (B : Finset (Fin e)) :
    S e B = ∑ k : Fin e, ((la e B k).toNat : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) := by
  rw [S, sum_pos_eq_sum_idx e he B (fun j => 2 ^ (j : ℕ))]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : sig e k ∈ B
  · rw [if_pos hk]
    have hla : la e B k = true := by simp [la, hk]
    rw [hla]
    simp only [Bool.toNat_true, Nat.cast_one, one_mul]
    exact (r_pow_eq e he k).symm
  · rw [if_neg hk]
    have hla : la e B k = false := by simp [la, hk]
    rw [hla]
    simp

private theorem sum_term_eq (e : ℕ) (he : Odd e) [NeZero e] (A B : Finset (Fin e))
    (x : Fin e → Bool × Bool × Bool)
    (hx : ∀ k : Fin e, x (k + 1) = stepB (la e A k) (la e B k) (la e B (k + 1)) (x k)) :
    S e B + ∑ q ∈ A, term e ((x ((Equiv.ofBijective (sig e) (sig_bijective e he)).symm q + 1)).2.2) q =
      ∑ k : Fin e, ((((la e B k).toNat : ℤ) + ((x k).2.2).toNat +
        own (la e A k) ((x (k + 1)).2.2) : ℤ) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) := by
  let σe : Fin e ≃ Fin e := Equiv.ofBijective (sig e) (sig_bijective e he)
  have hpend : ∀ k : Fin e, (x (k + 1)).2.2 = true → la e A k = true := by
    intro k hT
    have hstep : (stepB (la e A k) (la e B k) (la e B (k + 1)) (x k)).2.2 = true := by
      rw [← hx k]
      exact hT
    exact (stepB_pending (la e A k) (la e B k) (la e B (k + 1))
      (x k).1 (x k).2.1 (x k).2.2 hstep).1
  have hA_sum : ∑ q ∈ A, term e ((x (σe.symm q + 1)).2.2) q =
      ∑ k : Fin e, if la e A k = true then term e ((x (k + 1)).2.2) (sig e k) else 0 := by
    rw [sum_pos_eq_sum_idx e he A (fun q => term e ((x (σe.symm q + 1)).2.2) q)]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : sig e k ∈ A
    · have hla : la e A k = true := by simp [la, hk]
      rw [if_pos hk, if_pos hla]
      have hsym : σe.symm (sig e k) = k := σe.symm_apply_apply k
      rw [hsym]
    · have hla : la e A k = false := by simp [la, hk]
      rw [if_neg hk, if_neg (by simp [hla])]
  have hterm : ∀ k : Fin e,
      (if la e A k = true then term e ((x (k + 1)).2.2) (sig e k) else 0) =
      ((own (la e A k) ((x (k + 1)).2.2) : ℤ) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) +
        ((((x (k + 1)).2.2).toNat : ℤ) : ZMod (2 ^ e - 1)) * r e ^ ((k + 1 : Fin e) : ℕ) := by
    intro k
    rw [term_eq e he ((x (k + 1)).2.2) k]
    cases hla : la e A k <;> cases hb : (x (k + 1)).2.2
    · simp [hla, hb, own]
    · exact absurd (hpend k hb) (by rw [hla]; exact Bool.false_ne_true)
    · simp [hla, hb, own]
    · simp [hla, hb, own]
      ring
  have hshift : ∑ k : Fin e, ((((x (k + 1)).2.2).toNat : ℤ) : ZMod (2 ^ e - 1)) *
        r e ^ ((k + 1 : Fin e) : ℕ) =
      ∑ k : Fin e, ((((x k).2.2).toNat : ℤ) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) := by
    let φ : Fin e ≃ Fin e :=
      { toFun := fun k => k + 1
        invFun := fun k => k - 1
        left_inv := fun k => add_sub_cancel_right k 1
        right_inv := fun k => sub_add_cancel k 1 }
    have h := Equiv.sum_comp φ
      (fun k : Fin e => ((((x k).2.2).toNat : ℤ) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ))
    simpa [φ] using h
  have hS := S_eq_sum_idx e he B
  rw [hA_sum, hS]
  have hA' : ∑ k : Fin e, (if la e A k = true then term e ((x (k + 1)).2.2) (sig e k) else 0) =
      ∑ k : Fin e, (((own (la e A k) ((x (k + 1)).2.2) : ℤ) : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) +
        ((((x (k + 1)).2.2).toNat : ℤ) : ZMod (2 ^ e - 1)) * r e ^ ((k + 1 : Fin e) : ℕ)) :=
    Finset.sum_congr rfl fun k _ => hterm k
  rw [hA', Finset.sum_add_distrib, ← add_assoc, ← Finset.sum_add_distrib, hshift,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

private theorem run_recurrence (e : ℕ) (he : Odd e) [NeZero e] (A B : Finset (Fin e))
    (hI : IndepSigma e A) (x : Fin e → Bool × Bool × Bool)
    (hx : ∀ k : Fin e, x (k + 1) = stepB (la e A k) (la e B k) (la e B (k + 1)) (x k)) (k : Fin e) :
    ((la e B k).toNat : ℤ) + ((x k).2.2).toNat + own (la e A k) ((x (k + 1)).2.2) +
        ((x (k - 2 + 1)).2.1).toNat =
      (digB (la e A k) (la e B k) (x k)).toNat + 2 * ((x (k + 1)).2.1).toNat := by
  have hvalid : la e A k = true → (x k).2.2 = false :=
    fun h => run_valid e he A B hI x hx k h
  have hstep := stepB_arith (la e A k) (la e B k) (la e B (k + 1))
    (x k).1 (x k).2.1 (x k).2.2 hvalid
  have hb : (x k).1 = (x (k - 1)).2.1 := by
    have hkm1 : k - 1 + 1 = k := sub_add_cancel k 1
    conv_lhs => rw [← hkm1]
    exact congrArg (fun s => s.1) (hx (k - 1))
  have hkm2 : k - 2 + 1 = k - 1 := by
    have htwo : (2 : Fin e) = 1 + 1 := by norm_num
    rw [htwo, ← sub_sub, sub_add_cancel]
  have hfirst : (x (k - 2 + 1)).2.1 = (x k).1 := by
    rw [hkm2]
    exact hb.symm
  rw [hfirst, hx k]
  exact hstep

private theorem run_slots (e : ℕ) (he : Odd e) [NeZero e] (A B : Finset (Fin e))
    (hI : IndepSigma e A) (x : Fin e → Bool × Bool × Bool)
    (hx : ∀ k : Fin e, x (k + 1) = stepB (la e A k) (la e B k) (la e B (k + 1)) (x k)) (k : Fin e)
    (hk : la e A k = true) :
    if (x (k + 1)).2.2 = true then digB (la e A (k + 1)) (la e B (k + 1)) (x (k + 1)) = true
    else (digB (la e A k) (la e B k) (x k) = true ∨
      digB (la e A (k + 1)) (la e B (k + 1)) (x (k + 1)) = true) := by
  have hval := run_valid e he A B hI x hx k hk
  have hind := la_indep e he A hI k hk
  have hxk := hx k
  by_cases h1 : (x (k + 1)).2.2 = true
  · rw [if_pos h1]
    have h1' : (stepB (la e A k) (la e B k) (la e B (k + 1)) (x k)).2.2 = true := by
      rw [← hxk]
      exact h1
    have hres := stepB_slot_type (la e A k) (la e B k) (la e B (k + 1))
      (x k).1 (x k).2.1 (x k).2.2 hk hval h1'
    rw [hind, hxk]
    exact hres
  · rw [if_neg h1]
    have h1' : (x (k + 1)).2.2 = false := by
      cases hx2 : (x (k + 1)).2.2
      · rfl
      · exact absurd hx2 h1
    have h1'' : (stepB true (la e B k) (la e B (k + 1)) (x k)).2.2 = false := by
      rw [← hk, ← hxk]
      exact h1'
    have hres := stepB_slot_untyped (la e B k) (la e B (k + 1))
      (x k).1 (x k).2.1 (x k).2.2 hval h1''
    rw [hind, hxk, hk]
    exact hres

private theorem sum_ne_zero (e : ℕ) (he : Odd e) (A B : Finset (Fin e))
    (hAB : Disjoint (Lam e A) (Lam e B)) (t : Fin e → Bool) :
    S e B + ∑ q ∈ A, term e (t q) q ≠ 0 := by
  intro h0
  have hsB : ∑ q ∈ A, term e (t q) q = - S e B := by
    rw [add_comm] at h0
    exact add_eq_zero_iff_eq_neg.mp h0
  have hA : ∑ q ∈ A, term e (t q) q ∈ Lam e A := by
    refine ⟨fun j => if t j then R e else 1, ?_, ?_⟩
    · intro j hj
      cases htj : t j <;> simp [units, htj]
    · apply Finset.sum_congr rfl
      intro j hj
      cases htj : t j <;> simp [term, htj, mul_comm]
  have hB : ∑ q ∈ A, term e (t q) q ∈ Lam e B := by
    refine ⟨fun _ => -1, ?_, ?_⟩
    · intro j hj; simp [units]
    · rw [hsB, S, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
  exact (Set.disjoint_left.mp hAB) hA hB

theorem exists_slots_of_syncAt (e : ℕ) (he : Odd e) (h3 : 3 ≤ e) (A B : Finset (Fin e))
    (hI : IndepSigma e A) (hAB : Disjoint (Lam e A) (Lam e B)) (p : Fin e) (hp : SyncAt e A B p) :
    ∃ t : Fin e → Bool, Slots e A t (digits e (S e B + ∑ q ∈ A, term e (t q) q)) := by
  haveI : NeZero e := ⟨by omega⟩
  obtain ⟨x, hx⟩ := exists_run e he h3 A B p hp
  have hval := run_valid e he A B hI x hx
  let σe : Fin e ≃ Fin e := Equiv.ofBijective (sig e) (sig_bijective e he)
  let t : Fin e → Bool := fun q => (x (σe.symm q + 1)).2.2
  refine ⟨t, ?_⟩
  have hne := sum_ne_zero e he A B hAB t
  let y : Fin e → ℤ := fun k =>
    ((la e B k).toNat : ℤ) + ((x k).2.2).toNat + own (la e A k) ((x (k + 1)).2.2)
  let d : Fin e → ℤ := fun k => ((digB (la e A k) (la e B k) (x k)).toNat : ℤ)
  let c : Fin e → ℤ := fun k => (((x (k + 1)).2.1).toNat : ℤ)
  have hrec : ∀ k, y k + c (k - 2) = d k + 2 * c k := fun k => run_recurrence e he A B hI x hx k
  have htel := sum_digits_eq e he y d c hrec
  have hsum := sum_term_eq e he A B x hx
  let Dset : Finset (Fin e) := Finset.univ.filter fun k => digB (la e A k) (la e B k) (x k) = true
  have hDsum : ∑ k, (d k : ZMod (2 ^ e - 1)) * r e ^ (k : ℕ) = ∑ k ∈ Dset, r e ^ (k : ℕ) := by
    simp only [Dset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : digB (la e A k) (la e B k) (x k) = true <;> simp [d, h]
  have hD : S e B + ∑ q ∈ A, term e (t q) q = ∑ k ∈ Dset, r e ^ (k : ℕ) := by
    rw [← hDsum, htel]
    exact hsum
  have hdig := digits_eq_of_sum e he Dset _ hne hD
  rw [hdig]
  intro q hq
  obtain ⟨k, hkq⟩ := σe.surjective q
  have hkq' : sig e k = q := hkq
  subst hkq'
  have hk : la e A k = true := by simpa [la] using hq
  have htk : t (sig e k) = (x (k + 1)).2.2 := by
    simp only [t]
    have : σe.symm (sig e k) = k := σe.symm_apply_apply k
    rw [this]
  have hsucc : succσ e (sig e k) = sig e (k + 1) := (sig_add_one e he k).symm
  have hmem : ∀ j : Fin e, sig e j ∈ Dset.map ⟨sig e, (sig_bijective e he).1⟩ ↔
      digB (la e A j) (la e B j) (x j) = true := by
    intro j
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Dset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, h⟩
      rwa [← (sig_bijective e he).1 h]
    · intro h
      exact ⟨j, h, rfl⟩
  have hslot := run_slots e he A B hI x hx k hk
  rw [htk, hsucc]
  by_cases h1 : (x (k + 1)).2.2 = true
  · rw [if_pos h1]
    rw [if_pos h1] at hslot
    exact (hmem _).2 hslot
  · rw [if_neg h1]
    rw [if_neg h1] at hslot
    rcases hslot with h | h
    · exact Or.inl ((hmem _).2 h)
    · exact Or.inr ((hmem _).2 h)

end CFSG.StandardType.ReeB2Fixed
