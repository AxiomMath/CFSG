module

public import CFSG.Sporadic.Co1Patterson.IndexNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.QuasithinUnique

theorem sporadicThreePermuting_Co1
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤)
    (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Co1) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    simpa [CFSG.Quasithin.IsSylowIn, CFSG.QuasithinUnique.IsSylowTwoOf,
      Subgroup.relIndex] using hS
  exact exists_permutes_of_indexNinePackage
    (CFSG.Sporadic.Co1Patterson.IndexNine.co1_index_nine_package) e hS'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
