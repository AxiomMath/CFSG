module

public import CFSG.Quasithin.H13.AS91Sec1Replace

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94

universe u

variable {V : Type u} {Δ : SimpleGraph V} {C : Set (List V)}

theorem rot_moves_reverse {x : V} {T : List V} (hT : T.IsChain Δ.Adj) (hx : T.head? = some x)
    (hl : T.getLast? = some x) (h : Moves Δ C T [x]) : Moves Δ C T.reverse [x] := by
  obtain ⟨-, q, rfl⟩ := exists_cons_concat_of_head_last hx hl
  have h1 : Moves Δ C (q ++ [x] ++ q.reverse) (x :: q.reverse) := by
    simpa using Moves.context h [] q.reverse
  have h2 : Moves Δ C (q ++ [x] ++ q.reverse) [x] := by
    simpa using moves_backtrack_head (Δ := Δ) (C := C) hT hx
  rw [show (q ++ [x]).reverse = x :: q.reverse by simp]
  exact (Moves.symm h1).trans h2

theorem InClosure.of_isRotation {c d : List V} (hc : IsCycle Δ c) (hr : IsRotation c d)
    (h : InClosure Δ C c) : InClosure Δ C d := by
  obtain ⟨l₁, l₂, w, rfl, hw, rfl⟩ := hr
  obtain ⟨a, T, rfl⟩ : ∃ a T, l₁ = a :: T := by
    cases l₁ with
    | nil => simp at hw
    | cons a T => exact ⟨a, T, rfl⟩
  have hch : ((a :: T) ++ l₂).IsChain Δ.Adj := hc.1.2
  have hA : (a :: T).IsChain Δ.Adj := hch.left_of_append
  have hq : (T.reverse ++ [a]).IsChain Δ.Adj := by
    rw [show T.reverse ++ [a] = (a :: T).reverse by simp, List.isChain_reverse]
    exact hA.imp fun _ _ h => h.symm
  have hc0 : Moves Δ C ((a :: T) ++ l₂) [a] := InClosure.moves_head h (by simp)
  have hP : Moves Δ C ((T.reverse ++ [a] ++ T) ++ (l₂ ++ T)) (T.reverse ++ [a] ++ T) := by
    have h0 := Moves.context hc0 T.reverse T
    rwa [show T.reverse ++ ((a :: T) ++ l₂) ++ T = (T.reverse ++ [a] ++ T) ++ (l₂ ++ T) by simp]
      at h0
  have hw' : (T.reverse ++ [a]).head? = some w := by
    rw [show T.reverse ++ [a] = (a :: T).reverse by simp, List.head?_reverse, hw]
  have hB : Moves Δ C (T.reverse ++ [a] ++ T) [w] := by
    have key := moves_backtrack_head (Δ := Δ) (C := C) hq hw'
    rw [List.reverse_reverse] at key
    rw [show T.reverse ++ [a] ++ T = T.reverse ++ a :: T by simp]
    exact key
  have hR : Moves Δ C ((T.reverse ++ [a] ++ T) ++ (l₂ ++ T)) (w :: (l₂ ++ T)) :=
    Moves.context hB [] (l₂ ++ T)
  refine ⟨w, ?_⟩
  exact (Moves.symm hR).trans (hP.trans hB)

theorem InClosure.reverse {c : List V} (hc : IsCycle Δ c) (h : InClosure Δ C c) :
    InClosure Δ C c.reverse := by
  obtain ⟨⟨hne, hch⟩, hhl⟩ := hc
  obtain ⟨a, t, rfl⟩ : ∃ a t, c = a :: t := by
    cases c with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, t, rfl⟩
  have hx : (a :: t).head? = some a := rfl
  have hl : (a :: t).getLast? = some a := by rw [← hhl, hx]
  exact ⟨a, rot_moves_reverse hch hx hl (InClosure.moves_head h hx)⟩

end CFSG.Quasithin.H13.AS91
