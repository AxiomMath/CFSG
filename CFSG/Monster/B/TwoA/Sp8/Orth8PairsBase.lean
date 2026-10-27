
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

theorem zeros_span (k : Fin 8) :
    ∃ a b : V8, qPoly a = 0 ∧ qPoly b = 0 ∧ a + b = Pi.single k 1 := by
  fin_cases k
  · exact ⟨Pi.single 0 1, 0, by decide, by decide, by decide⟩
  · exact ⟨Pi.single 1 1, 0, by decide, by decide, by decide⟩
  · exact ⟨Pi.single 2 1, 0, by decide, by decide, by decide⟩
  · exact ⟨Pi.single 3 1, 0, by decide, by decide, by decide⟩
  · exact ⟨Pi.single 4 1, 0, by decide, by decide, by decide⟩
  · exact ⟨Pi.single 5 1, 0, by decide, by decide, by decide⟩
  · exact ⟨bvec 8 66, bvec 8 2, by decide, by decide, by decide⟩
  · exact ⟨bvec 8 129, bvec 8 1, by decide, by decide, by decide⟩

end CFSG.Monster.B.TwoA.Sp8
