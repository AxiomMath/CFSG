module

public import CFSG.Sporadic.SuzOddCore.IndexNine
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.Sporadic.SuzOddCore.SmallChain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Sporadic.SuzOddCore

theorem sporadicThreePermuting_Suz
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤)
    (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Suz) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  exact exists_permutes_of_indexNinePackage (Γ := ↥(suzM.subgroupOf suzT))
    suz_index_nine_package
    ((e.trans suzEquivM).trans (Subgroup.subgroupOfEquivOfLe suzM_le_suzT).symm) hS

theorem sporadicThreePermuting_Suz_of_card_center_three
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤)
    (hZ : Nat.card (Subgroup.center ↥K) = 3)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* CFSG.Blueprint.NativeSporadic.Suz) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  exact exists_permutes_of_indexThreePackage (Γ := ↥(suzM.subgroupOf suzT))
    suz_index_three_package hZ
    ((e.trans suzEquivM).trans (Subgroup.subgroupOfEquivOfLe suzM_le_suzT).symm) hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
