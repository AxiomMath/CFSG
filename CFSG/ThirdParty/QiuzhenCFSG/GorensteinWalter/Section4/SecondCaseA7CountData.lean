module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseAlternatingIndexBoundCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaDataDefs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7HInterMIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7CentralizerIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7CosetBound
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The A7 involution count data -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Package the total, base-coset, and outside-coset involution counts in the
A7 branch. -/
public theorem secondCase_a7_countData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d) :
    SecondCaseA7CountData w.M := by
  have hHrel :=
    secondCase_a7_H_inter_M_relIndex_eq_three
      hmin c w d hA7 hmodel
  have hMrel :=
    secondCase_a7_centralizer_index hmin c w d hA7 hmodel
  have hHtower :
      (c.H ⊓ w.M).relIndex c.H * c.H.index =
        (c.H ⊓ w.M).index :=
    Subgroup.relIndex_mul_index inf_le_left
  have hMtower :
      (c.H ⊓ w.M).relIndex w.M * w.M.index =
        (c.H ⊓ w.M).index :=
    Subgroup.relIndex_mul_index inf_le_right
  rw [hHrel] at hHtower
  rw [hMrel] at hMtower
  have hindex : c.H.index = 35 * w.M.index := by omega
  exact
    { involutions_card :=
        secondCase_total_involutions_card_of_H_index
          hmin c w.M hindex
      base_involutions_card :=
        secondCase_a7_base_involutions_card hmin c w d hA7 hmodel
      coset_involutions_bound := fun y hy hyM =>
        secondCase_a7_coset_involutions_card_le_21
          hmin c w d hA7 hmodel od hy hyM }

end CFSG.GorensteinWalter
