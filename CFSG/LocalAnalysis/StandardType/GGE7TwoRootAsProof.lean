module

public import CFSG.LocalAnalysis.StandardType.GGExcRootAsTorus
public import CFSG.LocalAnalysis.StandardType.GGExcRootAsGen
public import CFSG.LocalAnalysis.StandardType.GGIOneExcSmall

public section

namespace CFSG.StandardType.ExcRootAs

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.SeitzReduction.EPilot


theorem ggEndNodeRootEltBigAs_E7Two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : GGEndNodeRootEltBigAs 3 6 (adjointGroup .E7 K) := by
  have : Finite (adjointGroup .E7 K) := generated_group_finite .E7 K
  refine ggEndNodeRootEltBigAs_of_rootFusion
    (J := (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)) (D := perpLevi .E7 K)
    (fun As B hAs h7 hBAs h5 => exists_conj_mem_highRootSL2_E7_of_le hK hAs h7 hBAs h5)
    (fun X hXJ hX hcyc => ?_) CFSG.SeitzReduction.E7Pilot.isQuasisimple_perpLevi_E7
    CFSG.SeitzReduction.E7Pilot.center_perpLevi_E7_eq_bot (Or.inl (seven_dvd_card_perpLevi_E7 hK))
  have hXq : Nat.card X = Nat.card K + 1 := by rw [hX, hK]
  obtain ⟨hcen, -, hXD⟩ :=
    CFSG.SeitzReduction.E7Pilot.centralizer_nonsplit_E7_of_finite hXJ hXq hcyc
  exact ⟨hcen, hXD, fun c hc =>
    CFSG.SeitzReduction.E7Pilot.exists_mul_of_mem_centralizer_nonsplit_E7_of_finite hXJ hXq hcyc
      hc⟩

theorem ggE7TwoRootAsInput_holds : GGE7TwoRootAsInput := by
  intro K _ _ hK
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  exact ggEndNodeRootAs_recipe_of_eltBigAs (Or.inl rfl) hK (ggEndNodeRootEltBigAs_E7Two hK)

end CFSG.StandardType.ExcRootAs
