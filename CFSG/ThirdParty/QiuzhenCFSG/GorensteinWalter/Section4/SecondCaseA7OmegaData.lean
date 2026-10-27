module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaDataDefs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7EquationSix
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingIsPGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FixedCentralizerFromNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_c
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The A7 omega data

The order-three equation-(6) factors are the full fixed subgroups of the
chosen involution.  The Fitting subgroup is a noncyclic `3`-group, so
`lemma_4_5_c` supplies its characteristic noncyclic exponent-three omega
subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Construct the synchronized data used in the A7 equation-(8)
trichotomy. -/
public theorem secondCase_a7_omegaData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    Nonempty (SecondCaseA7OmegaData c w d) := by
  classical
  obtain ⟨K, B, s, hsI, hsH, hK_eq, _hKcyc, hB_eq, hjoinX, hKcard,
      hKleE, K0, F, hK0def, _hFdef, hF_eq, hjoinY, hFnormalM,
      hFcentE, _hFcyc, hK0card, hFcard⟩ :=
    secondCase_a7_equation6 hmin c w d hA7 hmodel
  have hK0leK : K0 ≤ K := by
    rw [hK0def]
    exact inf_le_right
  have hK0eqK : K0 = K :=
    Subgroup.eq_of_le_of_card_ge hK0leK (by rw [hK0card, hKcard])
  have hjoinKF : K ⊔ F = c.FU ⊓ w.M := by
    rw [← hK0eqK]
    exact hjoinY
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card F = 1 := by rw [hbot]; simp
    omega
  have hNFeq : Subgroup.normalizer (F : Set G) = w.M :=
    secondCase_normalizer_fitting_fixed_eq_M hmin c w F hFne hFnormalM
  have hFUp : IsPGroup 3 c.FU :=
    secondCase_a7_fitting_isPGroup_three hmin c w d hA7 hmodel
  have hfull := full_fixed_subgroups_of_normalizer_eq
    c.U c.FU w.M F B (s : G) hFUp
      (fittingSubgroupOf_isNormalIn c.U) hF_eq hB_eq hNFeq
  have hKFdisj : Disjoint K F := by
    rw [disjoint_iff]
    apply le_bot_iff.mp
    intro x hx
    have hxInv : (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
      have hxK : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
        rw [← hK_eq]
        exact hx.1
      exact hxK.2
    have hxFix : (s : G) * x * (s : G)⁻¹ = x := by
      have hxC : x ∈ centralizerIn c.FU (s : G) := by
        rw [← hfull.1]
        exact hx.2
      have hcomm : (s : G) * x = x * (s : G) :=
        (Subgroup.mem_centralizer_iff.mp hxC.2) (s : G) (by simp)
      rw [hcomm]
      group
    have hxSq : x ^ 2 = 1 := by
      have hxInvEq : x⁻¹ = x := hxInv.symm.trans hxFix
      calc
        x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := by rw [hxInvEq]
        _ = 1 := by simp
    let xF : F := ⟨x, hx.2⟩
    have hxFSq : xF ^ 2 = 1 := Subtype.ext hxSq
    have hcop : Nat.Coprime 2 (Nat.card F) := by
      rw [hFcard]
      decide
    have hxOne : xF = 1 :=
      eq_one_of_sq_eq_one_of_coprime_two hcop hxFSq
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxOne)
  have hFNormK : F ≤ Subgroup.normalizer (K : Set G) := by
    intro f hf
    exact Subgroup.centralizer_le_normalizer (K : Set G)
      (hFcentE.trans (Subgroup.centralizer_le (SetLike.coe_mono hKleE)) hf)
  have hjoinCard : Nat.card (K ⊔ F : Subgroup G) = 9 := by
    have hcard := card_sup_eq_mul_of_disjoint_of_le_normalizer
      K F hFNormK hKFdisj
    rw [hKcard, hFcard] at hcard
    norm_num at hcard ⊢
    exact hcard
  have hYcard : Nat.card ↥(c.FU ⊓ w.M) = 9 := by
    rw [← hjoinKF]
    exact hjoinCard
  have hFUncyc : ¬ IsCyclic c.FU := by
    intro hcyc
    let : IsCyclic c.FU := hcyc
    have hYle : c.FU ⊓ w.M ≤ c.FU := inf_le_left
    have hYsubcyc : IsCyclic ((c.FU ⊓ w.M).subgroupOf c.FU) :=
      Subgroup.isCyclic_of_le
        (show (c.FU ⊓ w.M).subgroupOf c.FU ≤ ⊤ by simp)
    have hYcyc : IsCyclic ↥(c.FU ⊓ w.M) :=
      (Subgroup.subgroupOfEquivOfLe hYle).isCyclic.mp hYsubcyc
    exact (secondCase_fitting_inter_M_not_cyclic hmin c w) hYcyc
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fact (IsPGroup 3 c.FU) := ⟨hFUp⟩
  let Z2 : Subgroup c.FU := Subgroup.upperCentralSeries c.FU 2
  let Om : Subgroup Z2 := omega₁ (G := Z2) (p := 3)
  let Q : Subgroup c.FU := z2OmegaCandidate (G := c.FU) 3
  obtain ⟨hOmnc, hOmexp⟩ :=
    lemma_4_5_c (R := c.FU) (p := 3) (by decide) hFUncyc
  let eQ : Om ≃* Q :=
    Subgroup.equivMapOfInjective Om Z2.subtype Z2.subtype_injective
  have hQnc : ¬ IsCyclic Q := by
    intro hQcyc
    exact hOmnc (eQ.isCyclic.mpr hQcyc)
  have hQexp : Monoid.exponent Q = 3 := by
    have he := Monoid.exponent_eq_of_mulEquiv eQ
    exact he.symm.trans hOmexp
  have hQchar : Q.Characteristic := by
    simpa [Q] using z2OmegaCandidate_characteristic (G := c.FU) 3
  exact ⟨
    { K := K
      B := B
      F := F
      s := s
      s_involution := hsI
      s_mem_H := hsH
      K_inverted := hK_eq
      B_fixed := hfull.2
      U_inter_M_eq := hjoinX
      K_card := hKcard
      K_le_E := hKleE
      F_fixed := hfull.1
      FU_inter_M_eq := hjoinKF
      FU_inter_M_card := hYcard
      F_normal_M := hFnormalM
      F_centralizes_E := hFcentE
      F_card := hFcard
      F_normalizer := hNFeq
      FU_isPGroup := hFUp
      Q := Q
      Q_le_upperCentralSeries_two := by
        simpa [Q] using
          z2OmegaCandidate_le_upperCentralSeries_two (G := c.FU) (p := 3)
      Q_not_cyclic := hQnc
      Q_exponent := hQexp
      Q_characteristic := hQchar }⟩

end CFSG.GorensteinWalter
