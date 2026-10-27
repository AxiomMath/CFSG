module

public import CFSG.LocalAnalysis.StandardType.GGExcRootAsTorus
public import CFSG.LocalAnalysis.StandardType.GGExcRootAsGen
public import CFSG.LocalAnalysis.StandardType.GGIOneExcSmall

public section

namespace CFSG.StandardType.ExcRootAs

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.SeitzReduction.EPilot


theorem seven_dvd_card_e7Levi {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : 7 ∣ Nat.card (CFSG.SeitzReduction.E8Pilot.e7Levi K) := by
  rw [Nat.card_congr (CFSG.SeitzReduction.E8Pilot.e7LeviEquiv K).toEquiv]
  exact (seven_dvd_card_perpLevi_E7 hK).trans (Subgroup.card_subgroup_dvd_card _)

theorem ggEndNodeRootEltBigAs_E8Two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : GGEndNodeRootEltBigAs 3 7 (adjointGroup .E8 K) := by
  have : Finite (adjointGroup .E8 K) := generated_group_finite .E8 K
  refine ggEndNodeRootEltBigAs_of_rootFusion
    (J := (highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K))
    (D := CFSG.SeitzReduction.E8Pilot.e7Levi K)
    (fun As B hAs h8 hBAs h6 => exists_conj_mem_highRootSL2_E8_of_le hK hAs h8 hBAs h6)
    (fun X hXJ hX hcyc => ?_) CFSG.SeitzReduction.E8Pilot.isQuasisimple_e7Levi
    CFSG.SeitzReduction.E8Pilot.center_e7Levi_eq_bot (Or.inl (seven_dvd_card_e7Levi hK))
  have hXq : Nat.card X = Nat.card K + 1 := by rw [hX, hK]
  obtain ⟨hcen, -, hXD⟩ := CFSG.SeitzReduction.E8Pilot.centralizer_nonsplit_E8 hXJ hXq hcyc
  exact ⟨hcen, hXD, fun c hc =>
    CFSG.SeitzReduction.E8Pilot.exists_mul_of_mem_centralizer_nonsplit_E8 hXJ hXq hcyc hc⟩

theorem ggE8TwoRootAsInput_holds : GGE8TwoRootAsInput := by
  intro K _ _ hK
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  exact ggEndNodeRootAs_recipe_of_eltBigAs (Or.inr rfl) hK (ggEndNodeRootEltBigAs_E8Two hK)

end CFSG.StandardType.ExcRootAs
