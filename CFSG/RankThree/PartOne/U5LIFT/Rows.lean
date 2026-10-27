module

public import CFSG.RankThree.PartOne.U5LIFT.Main
public import CFSG.RankThree.PartOne.U5LIFT.Row11
public import CFSG.RankThree.PartOne.S13K.Comm134

public section

namespace CFSG.RankThree.PartOne.U5LIFT

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.Assembly.LowTwoRank

theorem kfAt_row12 (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G 5 A c L E) (hF : Sec12Facts G 5 A c L E) (hEA : E ≠ A)
    (hrow : RowModel 5 L 12) :
    ∃ f : ℕ, RowModelF 5 L 12 f ∧
      ∀ t ∈ reflectionSet 5 E, t ∈ torusImage E L → KFAt 5 E f t := by
  obtain ⟨-, hZ, -⟩ := id hrow
  obtain ⟨f, K, _, hf1, h5, h25, hmod, ⟨C⟩⟩ := exists_ctx_row12 hGA h hF hEA hrow
  refine ⟨f, ⟨rfl, hZ, hf1, h5, h25, hmod⟩, fun t ht htL => ?_⟩
  obtain ⟨R, rfl⟩ := C.exists_refl ht htL
  exact C.refl_kfAt R

theorem kfLiftRow12 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFLiftRow 12 := by
  intro G _ _ p A c L E h hF hEA hrow t ht htL
  have hp5 : p = 5 := hrow.1
  subst hp5
  obtain ⟨f, -, hall⟩ := kfAt_row12 hGA h hF hEA hrow
  exact KFAt.toLiftAt (hall t ht htL)

theorem kfCommRow12 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFCommRow 12 := by
  intro G _ _ p A c L E h hF hEA hrow s hs hsL t ht htL hst hcomm
  have hp5 : p = 5 := hrow.1
  subst hp5
  obtain ⟨f, K, _, -, -, -, -, ⟨C⟩⟩ := exists_ctx_row12 hGA h hF hEA hrow
  obtain ⟨Rs, rfl⟩ := C.exists_refl hs hsL
  obtain ⟨Rt, rfl⟩ := C.exists_refl ht htL
  exact C.pair_comm Rs Rt hst hcomm

theorem kfAt_row11 (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G 5 A c L E) (hF : Sec12Facts G 5 A c L E) (hEA : E ≠ A)
    (hrow : RowModel 5 L 11) :
    ∃ f : ℕ, RowModelF 5 L 11 f ∧
      ∀ t ∈ reflectionSet 5 E, t ∈ torusImage E L → KFAt 5 E f t := by
  obtain ⟨-, hZ, -⟩ := id hrow
  obtain ⟨f, K, _, hf1, h5, hmod, ⟨C⟩⟩ := exists_ctx_row11 hGA h hF hEA hrow
  refine ⟨f, ⟨rfl, hZ, hf1, h5, hmod⟩, fun t ht htL => ?_⟩
  obtain ⟨R, rfl⟩ := C.exists_refl ht htL
  exact C.refl_kfAt R

theorem kfLiftRow11 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFLiftRow 11 := by
  intro G _ _ p A c L E h hF hEA hrow t ht htL
  have hp5 : p = 5 := hrow.1
  subst hp5
  obtain ⟨f, -, hall⟩ := kfAt_row11 hGA h hF hEA hrow
  exact KFAt.toLiftAt (hall t ht htL)

theorem kfCommRow11 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFCommRow 11 := by
  intro G _ _ p A c L E h hF hEA hrow s hs hsL t ht htL hst hcomm
  have hp5 : p = 5 := hrow.1
  subst hp5
  obtain ⟨f, K, _, -, -, -, ⟨C⟩⟩ := exists_ctx_row11 hGA h hF hEA hrow
  obtain ⟨Rs, rfl⟩ := C.exists_refl hs hsL
  obtain ⟨Rt, rfl⟩ := C.exists_refl ht htL
  exact C.pair_comm Rs Rt hst hcomm

end CFSG.RankThree.PartOne.U5LIFT
