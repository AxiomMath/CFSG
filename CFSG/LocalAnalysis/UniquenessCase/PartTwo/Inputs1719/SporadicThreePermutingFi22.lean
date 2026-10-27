module

public import CFSG.Monster.B.Fischer.Fi22IndexNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem sporadicThreePermuting_Fi22
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤)
    (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Fi22) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    simpa [CFSG.Quasithin.IsSylowIn, CFSG.QuasithinUnique.IsSylowTwoOf, Subgroup.relIndex] using hS
  exact exists_permutes_of_indexNinePackage CFSG.Monster.B.Fischer.fi22_index_nine_package
    ((e.trans CFSG.Monster.B.Fischer.fi22PermEquiv).trans
      (Subgroup.subgroupOfEquivOfLe CFSG.Monster.B.Fischer.fi22P_le_R).symm) hS'

theorem sporadicThreePermuting_Fi22_of_card_center_three
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤)
    (hZ : Nat.card (Subgroup.center ↥K) = 3)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* CFSG.Blueprint.NativeSporadic.Fi22) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    simpa [CFSG.Quasithin.IsSylowIn, CFSG.QuasithinUnique.IsSylowTwoOf, Subgroup.relIndex] using hS
  exact exists_permutes_of_indexThreePackage CFSG.Monster.B.Fischer.fi22_index_three_package hZ
    ((e.trans CFSG.Monster.B.Fischer.fi22PermEquiv).trans
      (Subgroup.subgroupOfEquivOfLe CFSG.Monster.B.Fischer.fi22P_le_R).symm) hS'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
