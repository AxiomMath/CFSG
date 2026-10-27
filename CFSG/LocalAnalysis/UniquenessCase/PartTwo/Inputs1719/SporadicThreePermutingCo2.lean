module

public import CFSG.Sporadic.Co2Schreier.IndexNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesInvariant

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

theorem sporadicThreePermuting_Co2
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤)
    (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Co2) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  obtain ⟨U, P, Q, hU, hUP, hP, hinv, hQP, hQ, hQ3⟩ :=
    CFSG.Sporadic.Co2Schreier.co2_index_nine_package
  exact exists_permutes_of_invariant_member hU hUP hP hinv hQP hQ hQ3
    (e.trans CFSG.Sporadic.Co2Cert.co2PermEquiv) hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
