module

public import CFSG.Quasithin.Recognition.UniquenessSystemMoves

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94

universe u

variable {V : Type u} {Δ : SimpleGraph V} {C : Set (List V)}

theorem _root_.CFSG.Quasithin.Asc94.ElemMove.getLast?_eq {p q : List V} (h : ElemMove Δ C p q) :
    p.getLast? = q.getLast? := by
  cases h with
  | backDel l₁ l₂ w v h => cases l₂ <;> simp [List.getLast?_append]
  | backIns l₁ l₂ w v h => cases l₂ <;> simp [List.getLast?_append]
  | cycIns l₁ l₂ c w hc h₁ h₂ => cases l₂ <;> simp [List.getLast?_append, List.getLast?_cons, h₂]
  | cycDel l₁ l₂ c w hc h₁ h₂ => cases l₂ <;> simp [List.getLast?_append, List.getLast?_cons, h₂]

theorem _root_.CFSG.Quasithin.Asc94.Moves.getLast?_eq {p q : List V} (h : Moves Δ C p q) :
    p.getLast? = q.getLast? := by
  induction h with
  | refl => rfl
  | tail _ hm ih => exact ih.trans hm.getLast?_eq

theorem moves_backtrack_head {q : List V} {w z : V} (hq : (q ++ [w]).IsChain Δ.Adj)
    (hz : (q ++ [w]).head? = some z) : Moves Δ C (q ++ w :: q.reverse) [z] := by
  have key := Moves.backtrack (Γ := Δ) (C := C) q w hq
  have e : (q ++ [w]).head (by simp) = z := (List.head_eq_iff_head?_eq_some _).mpr hz
  rw [e] at key
  exact key

theorem moves_out_back {x y : V} {s t : List V} (hc : (x :: s).IsChain Δ.Adj)
    (ht : (x :: s).reverse = y :: t) : Moves Δ C (y :: (t ++ s)) [y] := by
  have hL : s.reverse ++ [x] = y :: t := by
    rw [← List.reverse_cons]
    exact ht
  have h1 : (x :: s).reverse.IsChain Δ.Adj := by
    rw [List.isChain_reverse]
    exact hc.imp fun _ _ h => h.symm
  have hch : (s.reverse ++ [x]).IsChain Δ.Adj := by
    rw [← List.reverse_cons]
    exact h1
  have hz : (s.reverse ++ [x]).head? = some y := by
    rw [hL, List.head?_cons]
  have key : Moves Δ C (s.reverse ++ x :: s.reverse.reverse) [y] :=
    moves_backtrack_head hch hz
  rw [List.reverse_reverse] at key
  have e : y :: (t ++ s) = s.reverse ++ x :: s := by
    rw [← List.cons_append, ← hL, List.append_assoc, List.singleton_append]
  rw [e]
  exact key

theorem moves_of_inClosure {p q : List V} (hp : IsPath Δ p) (hq : IsPath Δ q)
    (hh : p.head? = q.head?) (hl : p.getLast? = q.getLast?)
    (h : InClosure Δ C (q ++ p.reverse.tail)) : Moves Δ C p q := by
  obtain ⟨x, s, rfl⟩ := List.exists_cons_of_ne_nil hp.1
  obtain ⟨q₀, y, rfl⟩ : ∃ q₀ y, q = q₀ ++ [y] := by
    rcases q.eq_nil_or_concat' with rfl | h'
    · exact (hq.1 rfl).elim
    · exact h'
  have hy : (x :: s).getLast? = some y := by
    rw [hl, List.getLast?_concat]
  have hq0 : (q₀ ++ [y]).head? = some x := by
    rw [← hh, List.head?_cons]
  have h1 : (x :: s).reverse.head? = some y := by
    rw [List.head?_reverse, hy]
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp h1
  have h2 : InClosure Δ C (q₀ ++ [y] ++ t) := by
    rw [ht, List.tail_cons] at h
    exact h
  have hc0 : (q₀ ++ [y] ++ t).head? = some x := by
    rw [List.head?_append, hq0, Option.some_or]
  have step1 : Moves Δ C (x :: s) (q₀ ++ [y] ++ t ++ s) := by
    have h3 : Moves Δ C (q₀ ++ [y] ++ t) [x] := InClosure.moves_head h2 hc0
    have h4 : Moves Δ C [x] (q₀ ++ [y] ++ t) := h3.symm
    simpa using h4.context [] s
  have hm : Moves Δ C (y :: (t ++ s)) [y] := moves_out_back hp.2 ht
  have step2 : Moves Δ C (q₀ ++ [y] ++ t ++ s) (q₀ ++ [y]) := by
    have e2 : q₀ ++ [y] ++ t ++ s = q₀ ++ (y :: (t ++ s)) := by simp
    rw [e2]
    simpa using hm.context q₀ []
  exact step1.trans step2

theorem moves_context_of_inClosure {p q : List V} (hp : IsPath Δ p) (hq : IsPath Δ q)
    (hh : p.head? = q.head?) (hl : p.getLast? = q.getLast?)
    (h : InClosure Δ C (q ++ p.reverse.tail)) (a b : List V) :
    Moves Δ C (a ++ p ++ b) (a ++ q ++ b) :=
  (moves_of_inClosure hp hq hh hl h).context a b

end CFSG.Quasithin.H13.AS91
