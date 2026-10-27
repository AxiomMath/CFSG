module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

namespace CFSG.Sporadic.Co1Schreier.Propagate

theorem list_sum_swap {R ι κ : Type*} [CommRing R] [Fintype ι] (N : κ → ι → R) (t : ι → R)
    (l : List κ) :
    (l.map fun e => ∑ v, t v * N e v).sum = ∑ v, t v * (l.map fun e => N e v).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero, Finset.sum_const_zero]
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, ih, mul_add, Finset.sum_add_distrib]

theorem eq_zero_of_steps {R ι κ : Type*} [CommRing R] [Fintype ι] (N : κ → ι → R)
    (rank : ι → ℕ) (S : ι → List κ)
    (hstep : ∀ u, 0 < rank u → ((S u).map fun e => N e u).sum = 1 ∧
      ∀ v, v ≠ u → rank u ≤ rank v → ((S u).map fun e => N e v).sum = 0)
    {t : ι → R} (ht : ∀ e, ∑ v, t v * N e v = 0) (hfree : ∀ u, rank u = 0 → t u = 0) :
    t = 0 := by
  have key : ∀ n, ∀ u, rank u = n → t u = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro u hu
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exact hfree u (hu.trans h0)
      · obtain ⟨h1, h2⟩ := hstep u (hu ▸ hpos)
        have hsum : ((S u).map fun e => ∑ v, t v * N e v).sum = 0 :=
          List.sum_eq_zero fun x hx => by
            obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
            exact ht e
        rw [list_sum_swap, Finset.sum_eq_single u] at hsum
        · rwa [h1, mul_one] at hsum
        · intro v _ hv
          by_cases hr : rank u ≤ rank v
          · rw [h2 v hv hr, mul_zero]
          · rw [ih (rank v) (by omega) v rfl, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ u) h
  funext u
  exact key _ u rfl

theorem xor_sum (f : ℕ → Bool) (l : List ℕ) : ∀ acc : Bool,
    (if acc then (1 : ZMod 2) else 0) + (l.map fun c => if f c then (1 : ZMod 2) else 0).sum =
      if l.foldl (fun b c => b ^^ f c) acc then 1 else 0 := by
  induction l with
  | nil => intro acc; rw [List.map_nil, List.sum_nil, add_zero, List.foldl_nil]
  | cons c l ih =>
    intro acc
    rw [List.map_cons, List.sum_cons, List.foldl_cons, ← ih, ← add_assoc]
    congr 1
    cases acc <;> cases f c <;> decide

end CFSG.Sporadic.Co1Schreier.Propagate
