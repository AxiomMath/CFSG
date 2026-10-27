module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingEqU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaData

namespace CFSG
end CFSG
open CFSG

/-! # Equality of the fixed subgroups in the A7 branch -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Once `F(U) = U`, the fixed subgroups of the chosen involution in those
two groups coincide. -/
public theorem secondCase_a7_fixed_subgroups_eq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d) :
    od.B = od.F := by
  rw [od.B_fixed, od.F_fixed,
    secondCase_a7_fitting_eq_U hmin c w d hA7 hmodel]

end CFSG.GorensteinWalter
