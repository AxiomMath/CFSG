module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.StandardType.FrameRoute.FS81.N7WtK

open Finset

@[expose] noncomputable def wtN (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.add acc
      (Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq (Nat.mod (Nat.div m (Nat.pow 3 i)) 3) 0))) 8

@[expose] noncomputable def cntW (f : ℕ → Bool) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun b acc => Nat.add acc (Nat.rec (motive := fun _ => ℕ) 0
      (fun a acc2 => Nat.add acc2
        (Bool.rec (motive := fun _ => ℕ) 0 1 (f (wtN (Nat.add a (Nat.mul 81 b)))))) 81)) 81

theorem rec_add_eq_sum (g : ℕ → ℕ) (k : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (g i)) k = ∑ i ∈ range k, g i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sum_range_succ, ← ih]
    rfl

theorem brec_beq_zero (x : ℕ) :
    Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq x 0) = if x = 0 then 0 else 1 := by
  cases hb : Nat.beq x 0
  · rw [if_neg (Nat.ne_of_beq_eq_false hb)]
  · rw [if_pos (Nat.eq_of_beq_eq_true hb)]

theorem brec_of_iff {p : Prop} [Decidable p] {b : Bool} (h : p ↔ b = true) :
    Bool.rec (motive := fun _ => ℕ) 0 1 b = if p then 1 else 0 := by
  cases b
  · rw [if_neg (fun hp => Bool.noConfusion (h.1 hp))]
  · rw [if_pos (h.2 rfl)]

theorem wtN_eq (m : ℕ) : wtN m = ∑ i : Fin 8, if m / 3 ^ (i : ℕ) % 3 = 0 then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if m / 3 ^ i % 3 = 0 then 0 else 1) 8, wtN,
    rec_add_eq_sum]
  exact Finset.sum_congr rfl fun i _ => brec_beq_zero _

theorem wt_eq_wtN (v : Fin 8 → ZMod 3) :
    wt v = wtN (finFunctionFinEquiv (m := 3) (n := 8) v : ℕ) := by
  rw [wtN_eq, wt, card_filter]
  refine sum_congr rfl fun i _ => ?_
  have hd : (finFunctionFinEquiv (m := 3) (n := 8) v : ℕ) / 3 ^ (i : ℕ) % 3 = (v i).val := by
    rw [← finFunctionFinEquiv_symm_apply_val]
    exact congrArg Fin.val
      (congrFun ((finFunctionFinEquiv (m := 3) (n := 8)).symm_apply_apply v) i)
  rw [hd]
  by_cases h : v i = 0
  · rw [if_neg (not_not.2 h), if_pos ((ZMod.val_eq_zero _).2 h)]
  · rw [if_pos h, if_neg (fun h' => h ((ZMod.val_eq_zero _).1 h'))]

theorem sum_range_mul81 (g : ℕ → ℕ) : ∀ B : ℕ,
    ∑ m ∈ range (81 * B), g m = ∑ b ∈ range B, ∑ a ∈ range 81, g (a + 81 * b)
  | 0 => by simp
  | B + 1 => by
    have e : ∑ x ∈ range 81, g (81 * B + x) = ∑ a ∈ range 81, g (a + 81 * B) :=
      Finset.sum_congr rfl fun a _ => by rw [Nat.add_comm]
    rw [Nat.mul_succ, Finset.sum_range_add g (81 * B) 81, sum_range_mul81 g B, e,
      Finset.sum_range_succ (fun b => ∑ a ∈ range 81, g (a + 81 * b)) B]

theorem card_filter_wt (p : ℕ → Prop) [DecidablePred p] (f : ℕ → Bool)
    (hf : ∀ k, p k ↔ f k = true) :
    (Finset.univ.filter fun v : Fin 8 → ZMod 3 => p (wt v)).card = cntW f := by
  have h1 : (Finset.univ.filter fun v : Fin 8 → ZMod 3 => p (wt v)).card =
      (Finset.univ.filter fun m : Fin (3 ^ 8) => p (wtN m)).card := by
    refine card_equiv (finFunctionFinEquiv (m := 3) (n := 8)) fun v => ?_
    simp only [mem_filter, mem_univ, true_and]
    exact Iff.of_eq (congrArg p (wt_eq_wtN v))
  rw [h1, card_filter, Fin.sum_univ_eq_sum_range (fun m => if p (wtN m) then 1 else 0) (3 ^ 8)]
  have h2 : (3 : ℕ) ^ 8 = 81 * 81 := by norm_num
  rw [h2, sum_range_mul81, cntW, rec_add_eq_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [rec_add_eq_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [brec_of_iff (p := p (wtN (Nat.add a (Nat.mul 81 b)))) (hf _)]
  rfl

end CFSG.StandardType.FrameRoute.FS81.N7WtK
