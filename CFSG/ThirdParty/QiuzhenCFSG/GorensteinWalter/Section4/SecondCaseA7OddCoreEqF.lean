module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FixedSubgroupsEq
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentCentralizesOddCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingOddCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra

namespace CFSG
end CFSG
open CFSG

/-! # The odd core of the maximal subgroup in the A7 branch -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- For the synchronized A7 data, the maximal subgroup's odd core is the
order-three fixed subgroup `F`. -/
public theorem secondCase_a7_oddCore_eq_F
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d) :
    oddCoreOf w.M = od.F := by
  have hFleFU : od.F ≤ c.FU :=
    le_sup_right.trans (od.FU_inter_M_eq.le.trans inf_le_left)
  have hFleO : od.F ≤ oddCoreOf w.M :=
    secondCase_a7_fitting_le_oddCore c w od.F hFleFU od.F_normal_M
  have hEcentO : d.E ≤ Subgroup.centralizer (oddCoreOf w.M : Set G) :=
    secondCase_component_centralizes_oddCore c w d
  have hOcentE : oddCoreOf w.M ≤ Subgroup.centralizer (d.E : Set G) :=
    Subgroup.le_centralizer_iff.mp hEcentO
  have hOleH : oddCoreOf w.M ≤ c.H := by
    intro x hx
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have hcomm :=
      (Subgroup.mem_centralizer_iff.mp (hOcentE hx)) c.t d.t_mem_E
    exact hcomm.symm
  have hOodd : Odd (Nat.card (oddCoreOf w.M)) :=
    odd_card_oddCoreOf w.M
  have hOleU : oddCoreOf w.M ≤ c.U :=
    odd_order_subgroup_le_U_of_H_eq_SU hmin c hOleH
      (Nat.coprime_two_left.mpr hOodd)
  have hOleB : oddCoreOf w.M ≤ od.B := by
    rw [od.B_fixed, centralizerIn]
    intro x hx
    exact ⟨hOleU hx,
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr od.s.2))
        (hOcentE hx)⟩
  have hB_eq_F : od.B = od.F :=
    secondCase_a7_fixed_subgroups_eq hmin c w d hA7 hmodel od
  exact le_antisymm (hOleB.trans hB_eq_F.le) hFleO

end CFSG.GorensteinWalter
