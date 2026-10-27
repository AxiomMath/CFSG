module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaStrictNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaInversionNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7NormalInvertedExclusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingEqU
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

namespace CFSG
end CFSG
open CFSG

/-! # Normality of the equation-(6) subgroup in the A7 case -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The subgroup `K F` from equation (6) is normal in `U` in the A7 case. -/
public theorem secondCase_a7_A_normal_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d) :
    IsNormalIn (od.K ⊔ od.F) c.U := by
  rcases secondCase_a7_omega_trichotomy c w d od with
    heq | ⟨hlt, _hQcard⟩ | ⟨hFnotleQ, hinvQ⟩
  · rw [heq]
    exact map_characteristic_isNormalIn_of_isNormalIn
      od.Q od.Q_characteristic (fittingSubgroupOf_isNormalIn c.U)
  · have hnormalFU := secondCase_a7_omega_strict_normal c w d od hlt
    rw [secondCase_a7_fitting_eq_U hmin c w d hA7 hmodel] at hnormalFU
    exact hnormalFU
  · obtain ⟨I, hIeq, hInormal⟩ :=
      secondCase_a7_omega_invertedElements_normal_Hhat
        hmin c w d od hFnotleQ hinvQ
    exact False.elim
      (secondCase_a7_inverted_subgroup_not_normal_Hhat
        hmin c w d hA7 hmodel od I hIeq hInormal)

end CFSG.GorensteinWalter
