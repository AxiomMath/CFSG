module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CenterlessCover
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentCenterLeFitting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPDvdKinv

namespace CFSG
end CFSG
open CFSG

/-!
# The linear component is centerless

Equation (7) makes the center of the selected component coprime to the field
cardinality.  The odd central-cover theorem for `PSL(2,q)` then proves the
source's equation-(9) conclusion `Z(E) = 1`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The centerless-cover consequence of the integrated post-nine data. -/
public theorem secondCase_linear_center_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (post : SecondCaseLinearPostNineData c w d K) :
    Subgroup.center d.E = ⊥ := by
  have hK0leE : post.od.K0 ≤ d.E := by
    intro x hx
    apply post.od.K_le_E
    rw [post.od.K0_eq] at hx
    exact hx.2
  have hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ post.od.F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E :=
    secondCase_linear_layer_eq_component_of_omegaData
      hmin c w d K hK e post.od post.hsS post.hsS0
  have hFMcoprime :
      Nat.Coprime (Nat.card (fittingSubgroupOf w.M)) (Nat.card K) :=
    secondCase_equationSevenPrime_fittingSubgroupOf_M_coprime
      hmin c w d K hK post.od.s post.od.K post.od.K0 post.od.F
      post.od.K_inverted post.od.K_cyclic post.od.K0_eq hK0leE
      post.od.F_fixed post.od.FU_inter_M_eq post.od.F_centralizes_E hLayer
      post.torus.T post.torus.T_card post.torus.T_odd_centralized_le
  have hZcoprime :
      Nat.Coprime (Nat.card (Subgroup.center d.E)) (Nat.card K) :=
    component_center_coprime_of_fitting_coprime
      w.M d.E d.E_component d.E_normal hFMcoprime
  have hpodd : Odd post.od.p :=
    secondCase_linear_omega_p_odd c w d post.od
  have hKseven : 7 ≤ Nat.card K :=
    secondCase_equationNine_q_ge_seven_of_p_dvd_Kinv
      d K post.equation9 post.od.hp_prime hpodd
        (secondCase_linear_p_dvd_Kinv c w d post)
  exact center_eq_bot_of_quasisimple_psl2_quotient_coprime
    d.E_component.2.2 K hK hKseven d.center_odd hZcoprime e

end CFSG.GorensteinWalter
