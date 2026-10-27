module

public import Certificates.Data.S1277Bfs
public import Mathlib.Data.Nat.Notation
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.SplitIfs

public section

namespace CFSG.Quasithin.H13.I1277

open Certificates.Data.S1277Bfs Std

theorem mem_foldl_insert (l : List ℕ) : ∀ (s : HashSet ℕ) (x : ℕ),
    x ∈ l.foldl (fun s x => s.insert x) s ↔ x ∈ s ∨ x ∈ l := by
  induction l with
  | nil => intro s x; simp
  | cons a l ih =>
    intro s x
    rw [List.foldl_cons, ih, HashSet.mem_insert]
    simp only [beq_iff_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr h

theorem pushNew_inv (P : ℕ → Prop) {seen : HashSet ℕ} {q : List ℕ} {y : ℕ}
    (hq : ∀ x ∈ q, P x) (hs : ∀ x ∈ seen, P x) (hy : P y) :
    (∀ x ∈ (pushNew seen q y).1, P x) ∧ (∀ x ∈ (pushNew seen q y).2, P x) := by
  unfold pushNew
  split_ifs with h
  · exact ⟨hq, hs⟩
  · refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact hy
      · exact hq x hx
    · rw [HashSet.mem_insert] at hx
      rcases hx with hx | hx
      · rw [beq_iff_eq] at hx
        rw [← hx]; exact hy
      · exact hs x hx

theorem pushNew_mono {seen : HashSet ℕ} {q : List ℕ} {y : ℕ} {x : ℕ} (hx : x ∈ seen) :
    x ∈ (pushNew seen q y).2 := by
  unfold pushNew
  split_ifs with h
  · exact hx
  · rw [HashSet.mem_insert]; exact Or.inr hx

theorem expand_inv (P : ℕ → Prop) (moves : List (ℕ → ℕ)) (hm : ∀ f ∈ moves, ∀ x, P x → P (f x))
    {x : ℕ} (hx : P x) :
    ∀ (ms : List (ℕ → ℕ)), (∀ f ∈ ms, f ∈ moves) → ∀ (q : List ℕ) (seen : HashSet ℕ),
      (∀ y ∈ q, P y) → (∀ y ∈ seen, P y) →
      (∀ y ∈ (ms.foldl (fun acc f => pushNew acc.2 acc.1 (f x)) (q, seen)).1, P y) ∧
      (∀ y ∈ (ms.foldl (fun acc f => pushNew acc.2 acc.1 (f x)) (q, seen)).2, P y) := by
  intro ms
  induction ms with
  | nil => intro _ q seen hq hs; exact ⟨hq, hs⟩
  | cons f ms ih =>
    intro hms q seen hq hs
    rw [List.foldl_cons]
    have h1 := pushNew_inv P (seen := seen) (q := q) (y := f x) hq hs
      (hm f (hms f (List.mem_cons_self)) x hx)
    exact ih (fun g hg => hms g (List.mem_cons_of_mem _ hg)) _ _ h1.1 h1.2

theorem expand_mono (moves : List (ℕ → ℕ)) (x : ℕ) :
    ∀ (ms : List (ℕ → ℕ)) (q : List ℕ) (seen : HashSet ℕ) (y : ℕ), y ∈ seen →
      y ∈ (ms.foldl (fun acc f => pushNew acc.2 acc.1 (f x)) (q, seen)).2 := by
  intro ms
  induction ms with
  | nil => intro q seen y hy; exact hy
  | cons f ms ih =>
    intro q seen y hy
    rw [List.foldl_cons]
    exact ih _ _ _ (pushNew_mono hy)

theorem bfsAux_inv (P : ℕ → Prop) (moves : List (ℕ → ℕ))
    (hm : ∀ f ∈ moves, ∀ x, P x → P (f x)) :
    ∀ (fuel : ℕ) (q : List ℕ) (seen : HashSet ℕ), (∀ x ∈ q, P x) → (∀ x ∈ seen, P x) →
      ∀ x ∈ bfsAux moves fuel q seen, P x := by
  intro fuel
  induction fuel with
  | zero => intro q seen _ hs; exact hs
  | succ n ih =>
    intro q seen hq hs
    cases q with
    | nil => exact hs
    | cons a q =>
      have h1 := expand_inv P moves hm (hq a List.mem_cons_self) moves (fun f hf => hf) q seen
        (fun y hy => hq y (List.mem_cons_of_mem _ hy)) hs
      exact ih _ _ h1.1 h1.2

theorem bfsAux_mono (moves : List (ℕ → ℕ)) :
    ∀ (fuel : ℕ) (q : List ℕ) (seen : HashSet ℕ) (y : ℕ), y ∈ seen →
      y ∈ bfsAux moves fuel q seen := by
  intro fuel
  induction fuel with
  | zero => intro q seen y hy; exact hy
  | succ n ih =>
    intro q seen y hy
    cases q with
    | nil => exact hy
    | cons a q => exact ih _ _ _ (expand_mono moves a moves q seen y hy)

theorem bfs_inv (P : ℕ → Prop) (moves : List (ℕ → ℕ)) (hm : ∀ f ∈ moves, ∀ x, P x → P (f x))
    (init : List ℕ) (hinit : ∀ x ∈ init, P x) (fuel : ℕ) : ∀ x ∈ bfs moves init fuel, P x := by
  refine bfsAux_inv P moves hm fuel init _ hinit ?_
  intro x hx
  rw [mem_foldl_insert] at hx
  rcases hx with hx | hx
  · simp at hx
  · exact hinit x hx

theorem mem_bfs_of_mem (moves : List (ℕ → ℕ)) {init : List ℕ} {x : ℕ} (hx : x ∈ init)
    (fuel : ℕ) : x ∈ bfs moves init fuel := by
  refine bfsAux_mono moves fuel init _ x ?_
  rw [mem_foldl_insert]
  exact Or.inr hx

end CFSG.Quasithin.H13.I1277

end
