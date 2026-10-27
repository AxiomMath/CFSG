module

public import CFSG.Quasithin.Recognition.UniquenessSystemTriangulation

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94

universe u

variable {V : Type u} {Δ : SimpleGraph V} {C : Set (List V)}

theorem inClosure_of_length_le_five {c : List V} (hc : IsCycle Δ c) (hlen : c.length ≤ 5) :
    InClosure Δ {p | IsNGon Δ 3 p ∨ IsNGon Δ 4 p} c := by
  obtain ⟨⟨hne, hch⟩, hhl⟩ := hc
  set S : Set (List V) := {p | IsNGon Δ 3 p ∨ IsNGon Δ 4 p}
  match c, hlen with
  | [], _ => exact absurd rfl hne
  | [w], _ => exact ⟨w, Relation.ReflTransGen.refl⟩
  | [a, b], _ =>
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at hhl
    exact absurd hhl (List.isChain_pair.mp hch).ne
  | [a, b, c'], _ =>
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at hhl
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    obtain ⟨hab, -⟩ := hch
    refine ⟨a, ?_⟩
    rw [← hhl]
    simpa using Moves.backDel (C := S) [] [] hab
  | [a, b, c', d], _ =>
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at hhl
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    obtain ⟨hab, hbc, hcd⟩ := hch
    rw [← hhl] at hcd ⊢
    exact inClosure_of_mem (isNGon_three hab hbc hcd).1 (Or.inl (isNGon_three hab hbc hcd))
  | [a, b, c', d, e], _ =>
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at hhl
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    obtain ⟨hab, hbc, hcd, hde⟩ := hch
    rw [← hhl] at hde ⊢
    by_cases hac : a = c'
    · rw [← hac]
      refine ⟨a, ?_⟩
      have h1 : Moves Δ S [a, b, a, d, a] [a, d, a] := by
        simpa using Moves.backDel (C := S) [] [d, a] hab
      have h2 : Moves Δ S [a, d, a] [a] := by
        simpa using Moves.backDel (C := S) [] [] hde.symm
      exact h1.trans h2
    by_cases hbd : b = d
    · rw [← hbd]
      refine ⟨a, ?_⟩
      have h1 : Moves Δ S [a, b, c', b, a] [a, b, a] := by
        simpa using Moves.backDel (C := S) [a] [a] hbc
      have h2 : Moves Δ S [a, b, a] [a] := by
        simpa using Moves.backDel (C := S) [] [] hab
      exact h1.trans h2
    exact inClosure_of_mem (isNGon_four hab hbc hcd hde hac hbd).1
      (Or.inr (isNGon_four hab hbc hcd hde hac hbd))
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp only [List.length_cons] at h <;> omega

theorem moves_triangle_shortcut (hC : ∀ p, IsNGon Δ 3 p → p ∈ C) (l₁ l₂ : List V) {x y z : V}
    (hxy : Δ.Adj x y) (hyz : Δ.Adj y z) (hxz : Δ.Adj x z) :
    Moves Δ C (l₁ ++ x :: y :: z :: l₂) (l₁ ++ x :: z :: l₂) := by
  have T : IsNGon Δ 3 [x, z, y, x] := isNGon_three hxz hyz.symm hxy.symm
  have m1 : Moves Δ C (l₁ ++ x :: y :: z :: l₂) (l₁ ++ [x, z, y, x] ++ (y :: z :: l₂)) :=
    Moves.cycIns_mem l₁ (y :: z :: l₂) [x, z, y, x] (hC _ T) rfl rfl
  have m2 : Moves Δ C (l₁ ++ [x, z, y, x] ++ (y :: z :: l₂))
      (l₁ ++ x :: z :: y :: z :: l₂) := by
    simpa using Moves.backDel (C := C) (l₁ ++ [x, z]) (z :: l₂) hxy.symm
  have m3 : Moves Δ C (l₁ ++ x :: z :: y :: z :: l₂) (l₁ ++ x :: z :: l₂) := by
    simpa using Moves.backDel (C := C) (l₁ ++ [x]) l₂ hyz.symm
  exact m1.trans (m2.trans m3)

end CFSG.Quasithin.H13.AS91
