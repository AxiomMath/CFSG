module

public import CFSG.Monster.Schur.M24.CheckPlain
public import CFSG.Monster.Schur.M24.Check0001
public import CFSG.Monster.Schur.M24.Check0010
public import CFSG.Monster.Schur.M24.Check0011
public import CFSG.Monster.Schur.M24.Check0100
public import CFSG.Monster.Schur.M24.Check0101
public import CFSG.Monster.Schur.M24.Check0110
public import CFSG.Monster.Schur.M24.Check0111
public import CFSG.Monster.Schur.M24.Check1000
public import CFSG.Monster.Schur.M24.Check1001
public import CFSG.Monster.Schur.M24.Check1010
public import CFSG.Monster.Schur.M24.Check1011
public import CFSG.Monster.Schur.M24.Check1100
public import CFSG.Monster.Schur.M24.Check1101
public import CFSG.Monster.Schur.M24.Check1110
public import CFSG.Monster.Schur.M24.Check1111

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_flags
    (b0 b1 b2 b3 b4 : Bool) (h : b0 = true ∨ b1 = true ∨ b2 = true ∨ b3 = true ∨ b4 = true) :
    Finite (PG (2 + 1) (epsRels U T5 ![b0, b1, b2, b3, b4])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![b0, b1, b2, b3, b4])) ≤ 244823040 := by
  cases b0 <;> cases b2 <;> cases b3 <;> cases b4
  · cases b1
    · simp at h
    · exact bound_r4
  · exact bound_0001 b1
  · exact bound_0010 b1
  · exact bound_0011 b1
  · exact bound_0100 b1
  · exact bound_0101 b1
  · exact bound_0110 b1
  · exact bound_0111 b1
  · exact bound_1000 b1
  · exact bound_1001 b1
  · exact bound_1010 b1
  · exact bound_1011 b1
  · exact bound_1100 b1
  · exact bound_1101 b1
  · exact bound_1110 b1
  · exact bound_1111 b1

theorem bound_eps
    (e : Fin 5 → Bool) (he : ∃ i, e i = true) :
    Finite (PG (2 + 1) (epsRels U T5 e)) ∧ Nat.card (PG (2 + 1) (epsRels U T5 e)) ≤ 244823040 := by
  have h : e = ![e 0, e 1, e 2, e 3, e 4] := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  obtain ⟨i, hi⟩ := he
  refine bound_flags _ _ _ _ _ ?_
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr (Or.inl hi))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hi)))

end CFSG.Monster.Schur.M24
