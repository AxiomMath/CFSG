module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingFixedCardLe

namespace CFSG
end CFSG
open CFSG

/-!
# Cyclicity of the A7 fitting fixed part

This compatibility wrapper exposes the cyclicity field of the stronger
equation-(6) cardinal transfer.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The equation-(3) fixed part is cyclic once equation (4) supplies its
normality and component centralization. -/
public theorem secondCase_a7_fitting_fixed_cyclic
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (K0 F : Subgroup G)
    (hK0cyc : IsCyclic K0)
    (hFleFU : F ≤ fittingSubgroupOf c.U)
    (hFnormalM : IsNormalIn F w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hjoin : K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M) :
    IsCyclic F :=
  (secondCase_a7_fitting_fixed_cyclic_and_card_le
    hmin c w d hA7 hmodel K0 F hK0cyc hFleFU hFnormalM hFcentE hjoin).1

end CFSG.GorensteinWalter
