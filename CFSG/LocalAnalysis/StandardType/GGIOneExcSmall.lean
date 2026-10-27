module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcRootAs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Two

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGE7TwoRootAsInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    GGEndNodeRootAs 3 6 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K)

@[expose] def GGE8TwoRootAsInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    GGEndNodeRootAs 3 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K)

@[expose] def GGF4TwoRootAsInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    GGEndNodeRootAs 3 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)

@[expose] def GGExcTwoCenterThreeInput : Prop :=
  (∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      GGCenterPrime 3 (TableBExc.RecipeGroup .E7 K)) ∧
  (∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      GGCenterPrime 3 (TableBExc.RecipeGroup .E8 K)) ∧
  (∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      GGCenterPrime 3 (TableBF4.RecipeGroup K))

section Certs


theorem ggIE_outdiagPrime_E7Two {K : Type} [Field K] [Finite K] [CharP K 2] :
    GGOutdiagPrime 3 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) :=
  fun _ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ

theorem ggIE_outdiagPrime_E8Two {K : Type} [Field K] :
    GGOutdiagPrime 3 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) :=
  fun _ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ

theorem ggIE_outdiagPrime_F4Two {K : Type} [Field K] :
    GGOutdiagPrime 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) :=
  fun _ hφ _ => TableBF4.idImage_subset_inn K hφ

theorem ggIE_labelAll_E7Two (hR : GGE7TwoRootAsInput)
    (hC : GGExcTwoCenterThreeInput) {lab : LargeEvenLabel} (htag : lab.tag = .E7)
    (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd 3 R I ∧
      ∃ r, GGTorusLift 3 r R ∧ GGEndNodeIOne 3 r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn
  subst htag hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggOutdiagOdd_of_prime (ggIE_outdiagPrime_E7Two (K := K)), 6,
    TableBExcTwo.ggTorusLift_E7Two,
    ggIE_endNodeIOne_of_rootAs_delta (hR K hK2)
      (ggEndNodeIOneDelta_of_prime ggIE_outdiagPrime_E7Two (hC.1 K hK2))⟩

theorem ggIE_labelAll_E8Two (hR : GGE8TwoRootAsInput)
    (hC : GGExcTwoCenterThreeInput) {lab : LargeEvenLabel} (htag : lab.tag = .E8)
    (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd 3 R I ∧
      ∃ r, GGTorusLift 3 r R ∧ GGEndNodeIOne 3 r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn
  subst htag hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggOutdiagOdd_of_prime (ggIE_outdiagPrime_E8Two (K := K)), 7,
    TableBExcTwo.ggTorusLift_E8Two,
    ggIE_endNodeIOne_of_rootAs_delta (hR K hK2)
      (ggEndNodeIOneDelta_of_prime ggIE_outdiagPrime_E8Two (hC.2.1 K hK2))⟩

theorem ggIE_labelAll_F4Two (hR : GGF4TwoRootAsInput)
    (hC : GGExcTwoCenterThreeInput) {lab : LargeEvenLabel} (htag : lab.tag = .F4)
    (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd 3 R I ∧
      ∃ r, GGTorusLift 3 r R ∧ GGEndNodeIOne 3 r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn
  subst htag hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggOutdiagOdd_of_prime (ggIE_outdiagPrime_F4Two (K := K)), 3,
    TableBF4Two.ggTorusLift_F4Two,
    ggIE_endNodeIOne_of_rootAs_delta (hR K hK2)
      (ggEndNodeIOneDelta_of_prime ggIE_outdiagPrime_F4Two (hC.2.2 K hK2))⟩

end Certs

end CFSG.StandardType
