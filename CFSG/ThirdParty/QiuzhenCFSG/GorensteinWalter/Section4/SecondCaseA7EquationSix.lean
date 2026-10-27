module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingInvolutionDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingNormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingOddCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingFixedCardLe
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingFixedNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingQuotientCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingQuotientBound
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7K0QuotientCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseInvertedOddCoreDisjoint
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentCentralizesOddCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMCardExactUnconditional
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseInvertedElementsInComponent
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The A7 equation-(6) decomposition

This module keeps one choice of all the equation-(1)--(3) witnesses while
adding the equation-(4)--(6) conclusions.  In particular, `K`, `K0`, and `F`
in the result belong to the same reflected decomposition.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch, the synchronized equation-(1)--(6) decomposition has
`|K| = |K0| = |F| = 3`, and the fixed part retains its normality and
component-centralization properties. -/
public theorem secondCase_a7_equation6
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    ∃ K B : Subgroup G, ∃ s : d.E,
      IsInvolution (s : G) ∧
      (s : G) ∈ c.H ∧
      (K : Set G) = invertedElements (c.U ⊓ w.M) (s : G) ∧
      IsCyclic K ∧
      B = centralizerIn (c.U ⊓ w.M) (s : G) ∧
      K ⊔ B = c.U ⊓ w.M ∧
      Nat.card K = 3 ∧
      K ≤ d.E ∧
      ∃ K0 F : Subgroup G,
        K0 = fittingSubgroupOf c.U ⊓ K ∧
        F = fittingSubgroupOf c.U ⊓ B ∧
        F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G) ∧
        K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M ∧
        IsNormalIn F w.M ∧
        F ≤ Subgroup.centralizer (d.E : Set G) ∧
        IsCyclic F ∧
        Nat.card K0 = 3 ∧
        Nat.card F = 3 := by
  classical
  obtain ⟨SM, hSMcent, SE, hSEamb, T, s, hsSE, hsI, hTcyc,
      hq_s_not_T, hTinv, hTcontain, hUEbar_le_T, hUEbar_cyclic,
      hUEbar_inv, K, B, hK_eq, hK_cyc, hB_def, hjoinX, K0, F,
      hK0_def, hF_def, hF_eq, hjoinY⟩ :=
    secondCase_fitting_involution_decomposition c w d
  let M : Subgroup G := w.M
  let O : Subgroup M := pPrimeCore 2 M
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  let X : Subgroup G := c.U ⊓ M
  let Y : Subgroup G := fittingSubgroupOf c.U ⊓ M
  have hsmap : (s : G) ∈ (SE : Subgroup d.E).map d.E.subtype :=
    Subgroup.mem_map.mpr ⟨s, hsSE, rfl⟩
  have hsSM : (s : G) ∈ ((SM : Subgroup w.M).map w.M.subtype) := by
    rw [hSEamb] at hsmap
    exact hsmap.1
  have hsH : (s : G) ∈ c.H := by
    rw [c.H_eq_centralizer]
    exact hSMcent hsSM
  have hsIG : IsInvolution (s : G) := by
    constructor
    · intro h1
      apply hsI.1
      apply Subtype.ext
      exact h1
    · simpa [pow_two] using congrArg Subtype.val hsI.2
  have hKleX : K ≤ X := by
    intro x hx
    change x ∈ (K : Set G) at hx
    rw [hK_eq] at hx
    simpa [X, M] using hx.1
  have hKleM : K ≤ M := hKleX.trans inf_le_right
  have hKleE : K ≤ d.E := by
    intro y hy
    have hyInv : y ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rw [← hK_eq]
      exact hy
    exact secondCase_invertedElements_le_component c w d SM hSMcent SE
      hSEamb hsSE hyInv.1.1 hyInv.1.2 hyInv.2
  have hK0leK : K0 ≤ K := by
    rw [hK0_def]
    exact inf_le_right
  have hK0leM : K0 ≤ M := hK0leK.trans hKleM
  have hK0cyc : IsCyclic K0 := by
    let : IsCyclic K := hK_cyc
    exact Subgroup.isCyclic_of_le hK0leK
  have hFleFU : F ≤ fittingSubgroupOf c.U := by
    rw [hF_def]
    exact inf_le_left
  have hFleM : F ≤ M := by
    intro f hf
    rw [hF_eq, centralizerIn] at hf
    exact hf.1.2
  have hFcentS : F ≤ Subgroup.centralizer ({(s : G)} : Set G) := by
    intro f hf
    rw [hF_eq, centralizerIn] at hf
    exact hf.2
  have hFcentE : F ≤ Subgroup.centralizer (d.E : Set G) :=
    secondCase_a7_fitting_centralizes_component_of_reflection
      c w d F hFleFU hFleM s hFcentS T hTinv hTcontain hA7
  have hFnormalM : IsNormalIn F M := by
    exact secondCase_a7_fitting_equation4
      c w d F hFleFU hFleM s hFcentS hF_eq T hTinv hTcontain hA7
  have hFcycCard : IsCyclic F ∧ Nat.card F ≤ Nat.card K0 := by
    exact secondCase_a7_fitting_fixed_cyclic_and_card_le
      hmin c w d hA7 hmodel K0 F hK0cyc hFleFU hFnormalM hFcentE hjoinY
  have hFne : F ≠ ⊥ := by
    exact secondCase_fitting_fixed_ne_bot
      hmin c w K K0 F hK_cyc hK0leK hjoinY
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hKodd : Odd (Nat.card K) :=
    Odd.of_dvd_nat hUodd
      (Subgroup.card_dvd_of_le (hKleX.trans inf_le_left))
  have hK0odd : Odd (Nat.card K0) :=
    Odd.of_dvd_nat hUodd
      (Subgroup.card_dvd_of_le
        (hK0leK.trans (hKleX.trans inf_le_left)))
  have hKinv : ∀ x : G, x ∈ K → (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
    intro x hx
    change x ∈ (K : Set G) at hx
    rw [hK_eq] at hx
    exact hx.2
  have hK0inv : ∀ x : G, x ∈ K0 → (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
    intro x hx
    exact hKinv x (hK0leK hx)
  have hEcentO : d.E ≤ Subgroup.centralizer (oddCoreOf M : Set G) := by
    simpa [M] using secondCase_component_centralizes_oddCore c w d
  have hKdisj : K ⊓ oddCoreOf M = ⊥ :=
    secondCase_inverted_inf_oddCore_eq_bot
      (M := M) (E := d.E) (K := K) (s : G) s.2 hEcentO hKodd hKinv
  have hK0disj : K0 ⊓ oddCoreOf M = ⊥ :=
    secondCase_inverted_inf_oddCore_eq_bot
      (M := M) (E := d.E) (K := K0) (s : G) s.2 hEcentO hK0odd hK0inv
  have hYleM : Y ≤ M := inf_le_right
  have hYleU : Y ≤ c.U := by
    intro y hy
    exact fittingSubgroupOf_le c.U hy.1
  have hYodd : Odd (Nat.card Y) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hYleU)
  have hYnotcyc : ¬ IsCyclic Y := by
    simpa [Y, M] using secondCase_fitting_inter_M_not_cyclic hmin c w
  have hK0infOmap : K0 ⊓ O.map M.subtype = ⊥ := by
    simpa [O, oddCoreOf] using hK0disj
  have hYcardle : Nat.card ((Y.subgroupOf M).map q) ≤ 3 := by
    simpa [Y, M, O, q] using
      secondCase_a7_fitting_quotient_card_le_three hmin c w d hA7 hmodel
  have hYcard : Nat.card ((Y.subgroupOf M).map q) = 3 := by
    exact secondCase_a7_fitting_quotient_card_eq_three_of_cyclic_fixed_part
      O Y K0 F hYleM hjoinY hK0infOmap hFcycCard.1 hYnotcyc hYodd hYcardle
  have hFleOmap : F ≤ O.map M.subtype := by
    simpa [M, O, oddCoreOf] using
      secondCase_a7_fitting_le_oddCore c w F hFleFU hFnormalM
  have hK0mapcard : Nat.card ((K0.subgroupOf M).map q) = 3 := by
    exact secondCase_a7_k0_quotient_card_eq_three
      O Y K0 F hYleM hjoinY hFleOmap hYcard
  have subgroupOf_inf_eq_bot
      (P : Subgroup G) (hPleM : P ≤ M)
      (hPinf : P ⊓ O.map M.subtype = ⊥) :
      P.subgroupOf M ⊓ O = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx.1
    have hxO : (x : G) ∈ O.map M.subtype :=
      Subgroup.mem_map.mpr ⟨x, hx.2, rfl⟩
    have hxbot : (x : G) ∈ P ⊓ O.map M.subtype := ⟨hxP, hxO⟩
    rw [hPinf] at hxbot
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hxbot
  have map_card_eq
      (P : Subgroup G) (hPleM : P ≤ M)
      (hPinf : P ⊓ O.map M.subtype = ⊥) :
      Nat.card ((P.subgroupOf M).map q) = Nat.card P := by
    have hInf : P.subgroupOf M ⊓ O = ⊥ :=
      subgroupOf_inf_eq_bot P hPleM hPinf
    have hformula := card_map_eq_card_mul_card_ker q (P.subgroupOf M)
    have hker : q.ker = O := by
      simp [q]
    rw [hker, hInf, Subgroup.card_bot, mul_one] at hformula
    have hsubcard : Nat.card (P.subgroupOf M) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleM).toEquiv
    exact hformula.symm.trans hsubcard
  have hK0mapEq : Nat.card ((K0.subgroupOf M).map q) = Nat.card K0 :=
    map_card_eq K0 hK0leM hK0infOmap
  have hK0card : Nat.card K0 = 3 := by
    rw [← hK0mapEq]
    exact hK0mapcard
  have hKinfOmap : K ⊓ O.map M.subtype = ⊥ := by
    simpa [O, oddCoreOf] using hKdisj
  have hKmapEq : Nat.card ((K.subgroupOf M).map q) = Nat.card K :=
    map_card_eq K hKleM hKinfOmap
  have hKsubleXsub : K.subgroupOf M ≤ X.subgroupOf M := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (hKleX (Subgroup.mem_subgroupOf.mp hx))
  have hKmaple : (K.subgroupOf M).map q ≤ (X.subgroupOf M).map q :=
    Subgroup.map_mono hKsubleXsub
  have hXmapcard : Nat.card ((X.subgroupOf M).map q) = 3 := by
    simpa [X, M, O, q] using
      secondCase_a7_u_inter_m_quotient_card_eq_three hmin c w d hA7 hmodel
  have hKmaple3 : Nat.card ((K.subgroupOf M).map q) ≤ 3 := by
    have hdiv := Subgroup.card_dvd_of_le hKmaple
    rw [hXmapcard] at hdiv
    exact Nat.le_of_dvd (by norm_num) hdiv
  have hKle3 : Nat.card K ≤ 3 := by
    rw [← hKmapEq]
    exact hKmaple3
  have hK0lecard : Nat.card K0 ≤ Nat.card K :=
    Nat.card_le_card_of_injective
      (Subgroup.inclusion hK0leK) (Subgroup.inclusion_injective hK0leK)
  have hKcard : Nat.card K = 3 := by
    omega
  have hFle3 : Nat.card F ≤ 3 := hFcycCard.2.trans_eq hK0card
  have hFodd : Odd (Nat.card F) :=
    Odd.of_dvd_nat hUodd
      (Subgroup.card_dvd_of_le (hFleFU.trans (fittingSubgroupOf_le c.U)))
  have hFcard : Nat.card F = 3 := by
    rcases hFodd with ⟨n, hn⟩
    have hcases : Nat.card F = 1 ∨ Nat.card F = 3 := by omega
    rcases hcases with h1 | h3
    · exact False.elim (hFne ((Subgroup.eq_bot_iff_card (H := F)).mpr h1))
    · exact h3
  refine ⟨K, B, s, hsIG, hsH, hK_eq, hK_cyc, hB_def, hjoinX, hKcard, hKleE,
    K0, F, hK0_def, hF_def, hF_eq, hjoinY, ?_, hFcentE,
    hFcycCard.1, hK0card, hFcard⟩
  simpa [M] using hFnormalM

end CFSG.GorensteinWalter
