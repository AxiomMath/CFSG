module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.Quasithin.Fan86

namespace P73

@[expose] def sh (v : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 := fun i => v (i - 1)

@[expose] def Wev (v : Fin 5 → ZMod 2) : Prop := ∑ i, v i = 0

instance : DecidablePred Wev := fun v => inferInstanceAs (Decidable (∑ i, v i = 0))

theorem cert : ∀ v w : Fin 5 → ZMod 2, (∃ i j, v i ≠ v j) → Wev w →
    ∃ c : Fin 5 → ZMod 2, w = ∑ k : Fin 5, c k • sh^[k.val] v := by
  decide +kernel

theorem ev_nonconst : ∀ v : Fin 5 → ZMod 2, Wev v → v ≠ 0 → ∃ i j, v i ≠ v j := by
  decide +kernel

theorem sh_ne : ∀ v : Fin 5 → ZMod 2, Wev v → v ≠ 0 → sh v ≠ v := by
  decide +kernel

theorem Wev_card : (Finset.univ.filter Wev).card = 16 := by decide +kernel

theorem const_cases : ∀ v : Fin 5 → ZMod 2, (∀ i j, v i = v j) → v = 0 ∨ v = 1 := by
  decide +kernel

theorem zmod_two_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem iter_mem (P : (Fin 5 → ZMod 2) → Prop) (hsh : ∀ a, P a → P (sh a))
    {v : Fin 5 → ZMod 2} (hv : P v) : ∀ k : ℕ, P (sh^[k] v) := by
  intro k
  induction k with
  | zero => exact hv
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hsh _ ih

theorem W_le (P : (Fin 5 → ZMod 2) → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsh : ∀ a, P a → P (sh a)) {v : Fin 5 → ZMod 2} (hv : P v) (hne : ∃ i j, v i ≠ v j)
    {w : Fin 5 → ZMod 2} (hw : Wev w) : P w := by
  obtain ⟨c, hc⟩ := cert v w hne hw
  rw [hc]
  refine Finset.sum_induction _ P hadd h0 fun k _ => ?_
  rcases zmod_two_cases (c k) with e | e
  · have : c k • sh^[k.val] v = 0 := by
      funext i
      simp [e]
    rw [this]
    exact h0
  · have : c k • sh^[k.val] v = sh^[k.val] v := by
      funext i
      simp [e]
    rw [this]
    exact iter_mem P hsh hv k.val

theorem eq_Wev (P : (Fin 5 → ZMod 2) → Prop) [DecidablePred P] (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b)) (hsh : ∀ a, P a → P (sh a)) {v : Fin 5 → ZMod 2}
    (hv : P v) (hne : ∃ i j, v i ≠ v j) (hcard : (Finset.univ.filter P).card ≤ 16) :
    ∀ w, P w ↔ Wev w := by
  have hsub : Finset.univ.filter Wev ⊆ Finset.univ.filter P := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact W_le P h0 hadd hsh hv hne hw
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Wev_card]; exact hcard)
  intro w
  have := congrArg (fun s => w ∈ s) heq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
  exact this.symm

end P73

end CFSG.Quasithin.Fan86
