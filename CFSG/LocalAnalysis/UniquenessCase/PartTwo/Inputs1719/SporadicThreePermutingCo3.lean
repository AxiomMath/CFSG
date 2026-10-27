module

public import CFSG.Sporadic.Schreier.Co3IndexNine
public import CFSG.Sporadic.Schreier.Co3Faithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

theorem sporadicThreePermuting_Co3
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Co3) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  obtain ⟨U, P, Q, hU, hUP, hP, hinv, hQP, hQ, hQ3⟩ :=
    CFSG.Sporadic.Schreier.Co3.co3_index_nine_package
  exact exists_permutes_of_invariant_member hU hUP hP hinv hQP hQ hQ3
    (e.trans CFSG.Sporadic.Schreier.Co3.co3PermEquiv) hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
