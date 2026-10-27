module

public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicThreeSixLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2CyclotomicComponent

public section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

theorem planeLocalCoreOdd_F4_cyclotomic_three_six {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1 ∨ p ∣ Nat.card K ^ 2 - Nat.card K + 1) :
    PlaneLocalCoreOdd p (adjointGroup .F4 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Finite (Module.End K (RootModule .F4 K)) := Module.finite_of_finite K
  intro B hB A hAB hA hAcard t htA ht1
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hE : IsElementaryAbelian p (A.subgroupOf B) := IsElementaryAbelian.subgroupOf hAB
  have hEcard : Nat.card (A.subgroupOf B) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, hAcard]
  have ht'E : (⟨t, hAB htA⟩ : B) ∈ A.subgroupOf B := Subgroup.mem_subgroupOf.2 htA
  have ht'1 : (⟨t, hAB htA⟩ : B) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  obtain ⟨-, hodd, -, -⟩ := odd_F4_cyclotomic_three_six_all_actors_local_core_product_odd hℓ hℓ2
    hf K hK hp hp3 hpd B hB (A.subgroupOf B) hE hEcard ⟨t, hAB htA⟩ ht'E ht'1
  have hAE : (A.subgroupOf B).map B.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAB]
  have heq : autPlaneProduct p B A t = (⁅inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨t, hAB htA⟩ : B)} : Set B)), A.subgroupOf B⁆ ⊔
        thetaT p (A.subgroupOf B)).map B.subtype := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, map_subtype_theta_centralizer hp B,
      ← autThetaT_eq_map_thetaT hp B (A.subgroupOf B) ht'E ht'1, hAE]
    rfl
  rw [heq, Subgroup.card_map_of_injective B.subtype_injective]
  exact hodd.not_two_dvd_nat

end CFSG.RankThree.Chevalley
