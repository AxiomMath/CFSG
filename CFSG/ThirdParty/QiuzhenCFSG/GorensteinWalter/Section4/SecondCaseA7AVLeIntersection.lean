module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7ANormalH
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7TwoCoreEquality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoCoreCentralizerEqualsHhat
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoCoreNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalSubgroupInfConjugate

namespace CFSG
end CFSG
open CFSG

/-! # The normal `A V` subgroup in the even coset intersection -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If an element lies in `H`, then the normal subgroup
`A V = (K F) O2(Hhat)` lies in `M ∩ M^y`. -/
public theorem secondCase_a7_A_sup_twoCore_le_inter_conjugate
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d)
    {y : G} (hyH : y ∈ c.H) :
    (od.K ⊔ od.F) ⊔ twoCoreOf c.Hhat ≤
      w.M ⊓ conjugateSubgroup w.M y := by
  let A : Subgroup G := od.K ⊔ od.F
  let V : Subgroup G := twoCoreOf c.Hhat
  have hAeq : A = c.U ⊓ w.M := by
    calc
      A = c.FU ⊓ w.M := by simpa [A] using od.FU_inter_M_eq
      _ = c.U ⊓ w.M := by
        rw [secondCase_a7_fitting_eq_U hmin c w d hA7 hmodel]
  have hAleM : A ≤ w.M := hAeq.le.trans inf_le_right
  have hAnormal : IsNormalIn A c.H := by
    simpa [A] using secondCase_a7_A_normal_H hmin c w d hA7 hmodel od
  have hVeqH : twoCoreOf c.H = V := by
    simpa [V] using
      twoCoreOf_H_eq_twoCoreOf_Hhat_of_centralizerStructure c
        (theorem_2_6 hmin c)
  have hVnormal : IsNormalIn V c.H := by
    rw [← hVeqH]
    exact twoCoreOf_isNormalIn c.H
  have hVleM : V ≤ w.M := by
    change twoCoreOf c.Hhat ≤ w.M
    rw [← secondCase_a7_twoCore_inter_eq_twoCore_Hhat
      hmin c w d hA7 hmodel]
    exact (Subgroup.map_subtype_le
      (pCore 2 (c.H ⊓ w.M : Subgroup G))).trans inf_le_right
  exact sup_le
    (normalSubgroup_le_inf_conjugateSubgroup hAnormal hAleM hyH)
    (normalSubgroup_le_inf_conjugateSubgroup hVnormal hVleM hyH)

end CFSG.GorensteinWalter
