module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesInvariant
public import CFSG.Sporadic.SmallOddCore.McLIndexNine
public import CFSG.Sporadic.Schreier.PairMcLFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

theorem sporadicThreePermuting_McL
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.McL) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  obtain ⟨U, P, Q, hU, hUP, hP, hinv, hQP, hQ, hQ3⟩ :=
    CFSG.Sporadic.SmallOddCore.mcl_index_nine_package
  exact exists_permutes_of_invariant_member hU hUP hP hinv hQP hQ hQ3
    (e.trans CFSG.Sporadic.Schreier.mclPermEquiv) hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
