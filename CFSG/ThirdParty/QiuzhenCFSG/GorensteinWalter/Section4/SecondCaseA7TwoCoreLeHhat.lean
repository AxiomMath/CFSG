module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7TwoCoreCentralizesU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoSubgroupCentralizingULeTwoCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26

namespace CFSG
end CFSG
open CFSG

/-!
# The forward equation-(7) two-core containment
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch, `O2(H \inter M)` lies in `O2(Hhat)`. -/
public theorem secondCase_a7_twoCore_inter_le_twoCore_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    twoCoreOf (c.H ⊓ w.M) ≤ twoCoreOf c.Hhat := by
  let C : Subgroup G := c.H ⊓ w.M
  let P : Subgroup G := twoCoreOf C
  have hPp : IsPGroup 2 P := by
    change IsPGroup 2 ((pCore 2 C).map C.subtype)
    exact (pCore_isPGroup (p := 2) (G := C)).map C.subtype
  have hPleHhat : P ≤ c.Hhat := by
    intro p hp
    rcases Subgroup.mem_map.mp hp with ⟨pC, hpC, rfl⟩
    exact c.H_le_Hhat pC.2.1
  have hPcentU : P ≤ Subgroup.centralizer (c.U : Set G) := by
    simpa [P, C] using
      secondCase_a7_twoCore_inter_centralizes_U hmin c w d hA7 hmodel
  exact twoSubgroup_le_twoCoreOf_Hhat_of_centralizes_U
    c (theorem_2_6 hmin c) P hPp hPleHhat hPcentU

end CFSG.GorensteinWalter
