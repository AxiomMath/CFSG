module

public import CFSG.Sporadic.Fi24.IndexNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem sporadicThreePermuting_Fi24
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [K.Normal] (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤)
    (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Fi24prime) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  exact exists_permutes_of_indexNinePackage (Γ := ↥CFSG.Sporadic.Fi24.J)
    CFSG.Sporadic.Fi24.fi24_index_nine_package (e.trans CFSG.Sporadic.Fi24.fi24EquivJ) hS

theorem sporadicThreePermuting_Fi24_of_card_center_three
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [K.Normal] (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤)
    (hZ : Nat.card (Subgroup.center ↥K) = 3)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* CFSG.Blueprint.NativeSporadic.Fi24prime) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  exact exists_permutes_of_indexThreePackage (Γ := ↥CFSG.Sporadic.Fi24.J)
    CFSG.Sporadic.Fi24.fi24_index_three_package hZ
    (e.trans CFSG.Sporadic.Fi24.fi24EquivJ) hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
