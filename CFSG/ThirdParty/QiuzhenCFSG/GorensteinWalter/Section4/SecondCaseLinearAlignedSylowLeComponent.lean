module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaDataOfAlignedSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearK0NormalAligned
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearLayerControl
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOuterTransportProducer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOuterDisjoint
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOuterContradiction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OuterParameter
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The aligned ambient Sylow lies in the PSL₂ component

Assuming otherwise produces the source's outer involution and its transported
odd reflected subgroup.  Equation (7) makes that subgroup disjoint from the
equation-(8) join, while equation (8) bounds the available index.  The even
and odd complementary field halves then give the numerical contradiction.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In a source-aligned second-case PSL₂ setup, the ambient Sylow subgroup is
contained in the selected component. -/
public theorem secondCase_linear_alignedSylow_le_component
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (SM : Sylow 2 (↥w.M))
    (hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤
      (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E) :
    (c.S : Subgroup G) ≤ d.E := by
  classical
  by_contra hSnotE
  obtain ⟨torus⟩ := secondCase_psl2_quotient_torus_card c w d K hK e
  obtain ⟨od, hsSE, hsS, hsS0, hF_eq, _hBcentSE, _hKnormSE,
      hKcomm⟩ :=
    secondCase_linear_omegaData_of_alignedSylow
      hmin c w d K hK e SM hSMleS SE hSEamb
  have hSMcent : (SM : Subgroup w.M).map w.M.subtype ≤
      Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
    exact hSMleS.trans (centralizerSetup_S_le_H c)
  have hK0normal : IsNormalIn od.K0 (c.H ⊓ w.M) :=
    secondCase_linear_K0_normal_H_inter_M_of_aligned_commutator
      hmin c w d K hK e SM hSMcent hSMleS SE hSEamb od hsSE hKcomm
  have hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ od.F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E :=
    secondCase_linear_layer_eq_component_of_omegaData
      hmin c w d K hK e od hsS hsS0
  have hm2 : 2 ≤ c.m :=
    secondCase_psl2_parameter_ge_two_of_aligned_not_le_component
      c w d K hK e SM hSMleS SE hSEamb hSnotE
  obtain ⟨r, R, hrSM, _hrI, _hrE, _htr, _hRcyc, hRodd, hRcard,
      hRleU, hRinv⟩ :=
    secondCase_linear_outer_transported_subgroup
      hmin c w d K hK e SM hSMleS SE hSEamb od.F hF_eq
        od.F_normalizer hSnotE hm2
  have hdisj : Disjoint (od.B ⊔ od.K ⊔ c.FU) R :=
    secondCase_linear_outer_disjoint
      hmin c w d K od torus SM hSMleS SE hSEamb hKcomm hK0normal
        hLayer r R hrSM hRodd hRcard hRinv
  have hrel : (od.B ⊔ od.K ⊔ c.FU).relIndex c.U ≤ od.p :=
    secondCase_linear_equationEight_relIndex_le_p hmin c w d od
  have hpdvdK0 : od.p ∣ Nat.card od.K0 := by
    rw [← od.P0_card]
    exact Subgroup.card_dvd_of_le od.P0_le_K0
  have hpdvdT : od.p ∣ Nat.card torus.T :=
    hpdvdK0.trans
      (secondCase_linear_K0_card_dvd_quotientTorus c w d K od torus)
  have hpodd : Odd od.p := secondCase_linear_omega_p_odd c w d od
  have h2pdvdT : 2 * od.p ∣ Nat.card torus.T :=
    (Nat.coprime_two_left.mpr hpodd).mul_dvd_of_dvd_of_dvd
      torus.T_even.two_dvd hpdvdT
  have hpk : 2 * od.p ≤ Nat.card torus.T :=
    Nat.le_of_dvd Nat.card_pos h2pdvdT
  have hk : Nat.card torus.T ≤ (Nat.card K + 1) / 2 := by
    rcases torus.T_card with hminus | hplus
    · rw [hminus]
      omega
    · rw [hplus]
  have hk' : (Nat.card K - 1) / 2 ≤ Nat.card R := by
    rcases hRcard with hminus | hplus
    · rw [hminus]
    · rw [hplus]
      omega
  have hp3 : 3 ≤ od.p := by
    have hp2 : 2 ≤ od.p := od.hp_prime.two_le
    rcases hpodd with ⟨a, ha⟩
    omega
  have hq : 7 ≤ Nat.card K := by
    omega
  exact secondCase_linear_reflected_card_contradiction
    c.U (od.B ⊔ od.K ⊔ c.FU) R od.p (Nat.card K)
      (Nat.card torus.T) (Nat.card R) hRleU hdisj hrel rfl hq hk hpk hk'

end CFSG.GorensteinWalter
