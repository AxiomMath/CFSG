module

public import CFSG.Quasithin.Recognition.UniquenessSystemTriangulation

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94

universe u

variable {V : Type u} {Δ : SimpleGraph V}

theorem moves_middle_of_reachable (l₁ l₂ : List V) {a b b' c : V} (hb : Δ.Adj a b ∧ Δ.Adj c b)
    (hb' : Δ.Adj a b' ∧ Δ.Adj c b')
    (hreach : (Δ.induce {v | Δ.Adj a v ∧ Δ.Adj c v}).Reachable ⟨b, hb⟩ ⟨b', hb'⟩) :
    Moves Δ {p | IsNGon Δ 3 p} (l₁ ++ a :: b :: c :: l₂) (l₁ ++ a :: b' :: c :: l₂) := by
  obtain ⟨p⟩ := hreach
  have key : ∀ (x y : {v | Δ.Adj a v ∧ Δ.Adj c v}),
      (Δ.induce {v | Δ.Adj a v ∧ Δ.Adj c v}).Walk x y →
      Moves Δ {p | IsNGon Δ 3 p} (l₁ ++ a :: (x : V) :: c :: l₂)
        (l₁ ++ a :: (y : V) :: c :: l₂) := by
    intro x y q
    induction q with
    | nil => exact Relation.ReflTransGen.refl
    | @cons x' y' z' hxy q' ih =>
      have hxy' : Δ.Adj x' y' := by simpa using hxy
      have step : Moves Δ {p | IsNGon Δ 3 p} (l₁ ++ a :: (x' : V) :: c :: l₂)
          (l₁ ++ a :: (y' : V) :: c :: l₂) :=
        moves_common_nbr_step x'.2.1 x'.2.2 y'.2.1 y'.2.2 hxy' l₁ l₂
      exact step.trans ih
  exact key ⟨b, hb⟩ ⟨b', hb'⟩ p

theorem inClosure_square_of_reachable {a b c d : V} (hab : Δ.Adj a b) (hbc : Δ.Adj b c)
    (hcd : Δ.Adj c d) (hda : Δ.Adj d a)
    (hreach : (Δ.induce {v | Δ.Adj a v ∧ Δ.Adj c v}).Reachable ⟨b, hab, hbc.symm⟩
      ⟨d, hda.symm, hcd⟩) :
    InClosure Δ {p | IsNGon Δ 3 p} [a, b, c, d, a] := by
  have m1 : Moves Δ {p | IsNGon Δ 3 p} [a, b, c, d, a] [a, d, c, d, a] := by
    simpa using moves_middle_of_reachable [] [d, a] ⟨hab, hbc.symm⟩ ⟨hda.symm, hcd⟩ hreach
  have m2 : Moves Δ {p | IsNGon Δ 3 p} [a, d, c, d, a] [a, d, a] := by
    simpa using Moves.backDel (C := {p | IsNGon Δ 3 p}) [a] [a] hcd.symm
  have m3 : Moves Δ {p | IsNGon Δ 3 p} [a, d, a] [a] := by
    simpa using Moves.backDel (C := {p | IsNGon Δ 3 p}) [] [] hda.symm
  exact ⟨a, m1.trans (m2.trans m3)⟩

end CFSG.Quasithin.H13.AS91
