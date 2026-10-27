module

public import CFSG.RankThree.PartOne.KC.UnitaryEndpointStatements
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

@[expose] def EvenUnitaryFivePlaneLocalCoreOdd : Prop :=
  ∀ (f : ℕ) {K : Type} [Field K] (h : UnitaryFieldData 2 f K), 5 ∣ 2 ^ f + 1 →
    PlaneLocalCoreOdd 5 (unitaryPSU h 5)

theorem even_unitary_five_actual_component_local_core_product_odd_action_of
    (hplane : EvenUnitaryFivePlaneLocalCoreOdd) :
    EvenUnitaryFiveActualComponentLocalCoreProductOddAction := by
  intro G _ _ f E hE hEcard t htE ht1 L hL hmod h5 hEL hSL
  have hp5 : Nat.Prime 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  obtain ⟨⟨-, hf, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  let φ : L ⧸ center L ≃* unitaryPSU hU 5 := e.trans (unitaryPSUEquiv hU (by norm_num)).symm
  have hplaneT : PlaneLocalCoreOdd 5 (L ⧸ center L) :=
    PlaneLocalCoreOdd.of_mulEquiv hp5 φ (hplane f hU h5)
  obtain ⟨hset, hWN, hrel, -, hnonfaith⟩ := component_local_core_odd_action_of_plane hp5 hp2 hE
    hEcard htE ht1 hL hEL hSL hplaneT
  exact ⟨⟨hset, hWN, hrel⟩, hnonfaith⟩

end CFSG.RankThree.PartOne
