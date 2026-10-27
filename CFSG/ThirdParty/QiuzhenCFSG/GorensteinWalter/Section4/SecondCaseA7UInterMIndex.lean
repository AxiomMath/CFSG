module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7ANormalU
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UNotLeM
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOrderNineSubgroupNormalizerIndex

namespace CFSG
end CFSG
open CFSG

/-! # The index of `U ∩ M` in `U` in the A7 case -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 case, `U ∩ M` has index three in `U`. -/
public theorem secondCase_a7_U_inter_M_relIndex_eq_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    (c.U ⊓ w.M).relIndex c.U = 3 := by
  obtain ⟨od⟩ := secondCase_a7_omegaData hmin c w d hA7 hmodel
  have hAnormal : IsNormalIn (od.K ⊔ od.F) c.U :=
    secondCase_a7_A_normal_U hmin c w d hA7 hmodel od
  have hAcard : Nat.card (od.K ⊔ od.F : Subgroup G) = 9 := by
    rw [od.FU_inter_M_eq]
    exact od.FU_inter_M_card
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hle :=
    odd_relIndex_inf_normalizer_le_three_of_normal_card_nine
      c.U (od.K ⊔ od.F) od.F hAnormal hAcard le_sup_right
        od.F_card hUodd
  rw [od.F_normalizer] at hle
  have hneOne : (c.U ⊓ w.M).relIndex c.U ≠ 1 := by
    intro hidx
    apply secondCase_a7_U_not_le_M hmin c w d hA7 hmodel
    exact (Subgroup.relIndex_eq_one.mp hidx).trans inf_le_right
  have hodd : Odd ((c.U ⊓ w.M).relIndex c.U) :=
    Odd.of_dvd_nat hUodd
      (Subgroup.relIndex_dvd_card (c.U ⊓ w.M) c.U)
  rcases hodd with ⟨k, hk⟩
  omega

end CFSG.GorensteinWalter
