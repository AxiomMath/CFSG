module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UIsPGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27FittingDecomposition

namespace CFSG
end CFSG
open CFSG

/-! # The Fitting subgroup is the odd core in the A7 branch -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch, the finite `3`-group `U` is nilpotent, so its Fitting
subgroup is all of `U`. -/
public theorem secondCase_a7_fitting_eq_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    c.FU = c.U := by
  have hp : IsPGroup 3 c.U :=
    secondCase_a7_U_isPGroup_three hmin c w d hA7 hmodel
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnil : Group.IsNilpotent c.U := hp.isNilpotent
  have htop : fittingSubgroup c.U = ⊤ :=
    fittingSubgroup_eq_top_of_isNilpotent hnil
  change (fittingSubgroup c.U).map c.U.subtype = c.U
  rw [htop]
  ext x
  simp

end CFSG.GorensteinWalter
