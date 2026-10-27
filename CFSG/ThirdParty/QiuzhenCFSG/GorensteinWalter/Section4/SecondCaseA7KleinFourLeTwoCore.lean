module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7AmbientKleinFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7TwoSubgroupCentralizesU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoSubgroupCentralizingULeTwoCore

namespace CFSG
end CFSG
open CFSG

/-!
# A Klein four inside O2(Hhat) in the A7 branch
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch, `O2(Hhat)` contains a Klein four subgroup. -/
public theorem secondCase_a7_exists_kleinFour_le_twoCore_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    ∃ V : Subgroup G, IsKleinFour V ∧ V ≤ twoCoreOf c.Hhat := by
  obtain ⟨V, hVK, hVleC, hVcentY⟩ :=
    secondCase_a7_exists_ambient_kleinFour_centralizing_fitting_inter
      hmin c w d hA7 hmodel
  have hVp : IsPGroup 2 V := by
    apply IsPGroup.of_card (n := 2)
    simpa [Nat.card_eq_fintype_card] using hVK.card_four
  have hVcentU : V ≤ Subgroup.centralizer (c.U : Set G) :=
    secondCase_a7_twoSubgroup_centralizes_U_of_centralizes_fitting_inter
      hmin c w d hA7 hmodel V hVp hVleC hVcentY
  have hVleHhat : V ≤ c.Hhat :=
    hVleC.trans (inf_le_left.trans c.H_le_Hhat)
  have hVleCore : V ≤ twoCoreOf c.Hhat :=
    twoSubgroup_le_twoCoreOf_Hhat_of_centralizes_U
      c (theorem_2_6 hmin c) V hVp hVleHhat hVcentU
  exact ⟨V, hVK, hVleCore⟩

end CFSG.GorensteinWalter
