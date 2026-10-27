module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearComponentCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2AlignedSylowDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FittingInnerAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerFittingAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerLayerEquality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseConjugator
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseInvertedElementsInComponent
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingInterNotCyclic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingFixedNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostEquationFour
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FixedCentralizerFromNilpotentNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_c
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The aligned linear omega-data producer

This module assembles the equations-(1)--(7) PSL₂ branch from explicitly
aligned Sylow subgroups, without assuming the global fixed ambient Sylow is
contained in the selected component. It then constructs the characteristic
noncyclic omega subgroup used by equation (8).
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Construct synchronized linear omega data from a Sylow subgroup `SM` of
`M` aligned inside the ambient Sylow `S`, and a component Sylow subgroup
`SE = SM ∩ E`. This is the source-faithful producer used before the later
argument establishing the re-chosen ambient containment `S ≤ E`.  In
addition to the equation-(1)--(7) data, its final conjunct records the exact
commutator identity for the selected component Sylow. -/
public theorem secondCase_linear_omegaData_of_alignedSylow
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (SM0 : Sylow 2 (↥w.M))
    (hSM0leS : (SM0 : Subgroup w.M).map w.M.subtype ≤
      (c.S : Subgroup G))
    (SE0 : Sylow 2 (↥d.E))
    (hSE0amb : (SE0 : Subgroup d.E).map d.E.subtype =
      ((SM0 : Subgroup w.M).map w.M.subtype) ⊓ d.E) :
    ∃ od : SecondCaseLinearOmegaData c w d,
      od.s ∈ (SE0 : Subgroup d.E) ∧
        (od.s : G) ∈ (c.S : Subgroup G) ∧
        (od.s : G) ∉ c.S0 ∧
        od.F = c.FU ⊓ Subgroup.centralizer
          (((SE0 : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G) ∧
        od.B ≤ Subgroup.centralizer
          (((SE0 : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G) ∧
        ((SE0 : Subgroup d.E).map d.E.subtype) ≤
          Subgroup.normalizer (od.K : Set G) ∧
        od.K = ⁅(SE0 : Subgroup d.E).map d.E.subtype, c.U ⊓ w.M⁆ := by
  classical
  obtain ⟨ad⟩ := secondCase_psl2_action_data hmin c w d K hK e
  obtain ⟨torus⟩ := secondCase_psl2_quotient_torus_card c w d K hK e
  obtain ⟨hSMcent, hSEamb, T, s, hsSE, hsI, hTcyc, _htT, _hsnotT,
      _hPdecomp, _hnormalizer, hTinv, hTcontain, _hUEleT, _hUEcyc,
      _hUEinv, hsS, hsS0,
      Kinv, B, hKinv, hKcyc, hBfixed, hBcentSE, _hKleE, _hKmap,
      _hKcenter, hKnormSE, hjoinX, K0, F, hK0def, _hFdef, hFfixed,
      hjoinY⟩ :=
    secondCase_psl2_alignedSylow_decomposition
      hmin c w d K hK e SM0 hSM0leS SE0 hSE0amb
  have hsIG : IsInvolution (s : G) := by
    constructor
    · intro hs1
      exact hsI.1 (Subtype.ext hs1)
    · simpa using congrArg Subtype.val hsI.2
  have hsH : (s : G) ∈ c.H := centralizerSetup_S_le_H c hsS
  have hKleE : Kinv ≤ d.E := _hKleE
  have hK0leK : K0 ≤ Kinv := by
    rw [hK0def]
    exact inf_le_right
  have hFleFU : F ≤ c.FU := by
    intro f hf
    rw [hFfixed] at hf
    exact hf.1.1
  have hFleM : F ≤ w.M := by
    intro f hf
    rw [hFfixed] at hf
    exact hf.1.2
  have hFcentS : F ≤ Subgroup.centralizer ({(s : G)} : Set G) := by
    intro f hf
    rw [hFfixed] at hf
    exact hf.2
  have hrefl : c.IsReflection (s : G) := ⟨hsS, hsS0⟩
  have hinner : secondCase_psl2_fitting_innerAction d K ad F hFleM :=
    secondCase_psl2_fitting_innerAction_of_actionData
      d K ad torus F hFleFU hFleM
  have hFcentE : F ≤ Subgroup.centralizer (d.E : Set G) :=
    secondCase_psl2_fitting_centralizes_component
      c w d F hFleFU hFleM s hrefl hFcentS T hTinv hTcontain K ad hinner
  have hFnormalM : IsNormalIn F w.M :=
    secondCase_psl2_fitting_equation4
      c w d F hFleFU hFleM s hrefl hFcentS hFfixed T hTinv hTcontain
      K ad hinner
  have hFne : F ≠ ⊥ :=
    secondCase_fitting_fixed_ne_bot hmin c w Kinv K0 F hKcyc hK0leK hjoinY
  have hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E := by
    intro X hXne hXleF
    have hcentral := secondCase_psl2_normalizer_fitting_action
      hmin c w d K hK e F X s hFfixed hrefl hFleFU hFleM hFcentE
      hXne hXleF
    exact secondCase_psl2_normalizer_layer_eq_component
      hmin c w d K hK e F X hFleFU hFleM hFcentE hFnormalM hFne
      hXne hXleF hcentral
  obtain ⟨hFnormalM', hFnormalY, _hFne', hNF, hFTI, hFcyc,
      _hFcardle, hK0ne, _hO2⟩ :=
    secondCase_fitting_equation5_7_of_component_centralization
      hmin c w d Kinv K0 F s hKcyc hK0leK hFfixed hjoinY hFcentE hLayer
  have hFcarddvd : Nat.card F ∣ Nat.card K0 := by
    obtain ⟨g, hgY, hgnotM⟩ := secondCase_exists_conjugator_not_mem_M hmin c w
    exact secondCase_fitting_fixed_part_card_dvd_of_conjugate_disjoint
      K0 F (c.FU ⊓ w.M) hFnormalY hjoinY g hgY (hFTI g hgnotM)
  have hFcardne : Nat.card F ≠ 1 := by
    intro hcard
    exact hFne ((Subgroup.eq_bot_iff_card (H := F)).mpr hcard)
  obtain ⟨p, hp, hpdvdF⟩ := Nat.exists_prime_and_dvd hFcardne
  let : Fact p.Prime := ⟨hp⟩
  have hFleU : F ≤ c.U := hFleFU.trans (fittingSubgroupOf_le c.U)
  have hpdvdU : p ∣ Nat.card c.U :=
    hpdvdF.trans (Subgroup.card_dvd_of_le hFleU)
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hpodd : Odd p := Odd.of_dvd_nat hUodd hpdvdU
  have hpne2 : p ≠ 2 := by
    intro hp2
    apply hpodd.not_two_dvd_nat
    rw [hp2]
  obtain ⟨f, hforder⟩ := exists_prime_orderOf_dvd_card' (G := F) p hpdvdF
  let P : Subgroup G := Subgroup.zpowers (f : G)
  have hforderG : orderOf (f : G) = p :=
    (orderOf_injective F.subtype F.subtype_injective f).trans hforder
  have hPcard : Nat.card P = p := by
    rw [Nat.card_zpowers, hforderG]
  have hPleF : P ≤ F := by
    exact Subgroup.zpowers_le.mpr f.2
  have hpdvdK0 : p ∣ Nat.card K0 := hpdvdF.trans hFcarddvd
  obtain ⟨f0, hf0order⟩ := exists_prime_orderOf_dvd_card' (G := K0) p hpdvdK0
  let P0 : Subgroup G := Subgroup.zpowers (f0 : G)
  have hf0orderG : orderOf (f0 : G) = p :=
    (orderOf_injective K0.subtype K0.subtype_injective f0).trans hf0order
  have hP0card : Nat.card P0 = p := by
    rw [Nat.card_zpowers, hf0orderG]
  have hP0leK0 : P0 ≤ K0 := by
    exact Subgroup.zpowers_le.mpr f0.2
  have hFK0bot : F ⊓ K0 = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxfix : (s : G) * x * (s : G)⁻¹ = x := by
      have hxmem : x ∈ centralizerIn (c.FU ⊓ w.M) (s : G) := by
        have hxmem' := hx.1
        rw [hFfixed] at hxmem'
        simpa [CentralizerSetup.FU] using hxmem'
      have hcomm : (s : G) * x = x * (s : G) :=
        (Subgroup.mem_centralizer_iff.mp hxmem.2) (s : G) (by simp)
      calc
        (s : G) * x * (s : G)⁻¹ = x * (s : G) * (s : G)⁻¹ := by rw [hcomm]
        _ = x := by simp
    have hxinv : (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
      have hxK : x ∈ Kinv := hK0leK hx.2
      have hxI : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
        rw [← hKinv]
        exact hxK
      exact hxI.2
    have hx2 : x ^ 2 = 1 := by
      have hxeq : x = x⁻¹ := hxfix.symm.trans hxinv
      calc
        x ^ 2 = x * x := by rw [pow_two]
        _ = x * x⁻¹ := congrArg (fun y : G => x * y) hxeq
        _ = 1 := by simp
    have hxU : x ∈ c.U := hFleU hx.1
    have hdiv2 : orderOf x ∣ 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := x) (n := 2)).mpr hx2
    have hdivU : orderOf x ∣ Nat.card c.U :=
      Subgroup.orderOf_dvd_natCard c.U hxU
    have hcop : Nat.Coprime 2 (Nat.card c.U) :=
      Nat.coprime_two_left.mpr hUodd
    have hord1 : orderOf x ∣ 1 := by
      simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hdiv2 hdivU
    exact Subgroup.mem_bot.mpr
      ((orderOf_eq_one_iff (x := x)).mp (Nat.dvd_one.mp hord1))
  have hPdisjP0 : Disjoint P P0 := by
    rw [disjoint_iff]
    apply le_bot_iff.mp
    intro x hx
    have hxFK0 : x ∈ F ⊓ K0 := ⟨hPleF hx.1, hP0leK0 hx.2⟩
    rw [hFK0bot] at hxFK0
    exact hxFK0
  have hP0centP : P0 ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hycent : y ∈ Subgroup.centralizer (d.E : Set G) :=
      hFcentE (hPleF hy)
    exact (Subgroup.mem_centralizer_iff.mp hycent x
      (hKleE (hK0leK (hP0leK0 hx)))).symm
  have hP0normP : P0 ≤ Subgroup.normalizer (P : Set G) :=
    hP0centP.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  let A : Subgroup G := P ⊔ P0
  have hAcard : Nat.card A = p ^ 2 := by
    rw [show A = P ⊔ P0 by rfl,
      card_sup_eq_mul_of_disjoint_of_le_normalizer P P0 hP0normP hPdisjP0,
      hPcard, hP0card, pow_two]
  have hfpow : (f : G) ^ p = 1 := by
    exact (orderOf_dvd_iff_pow_eq_one (x := (f : G)) (n := p)).mp
      (by rw [hforderG])
  have hf0pow : (f0 : G) ^ p = 1 := by
    exact (orderOf_dvd_iff_pow_eq_one (x := (f0 : G)) (n := p)).mp
      (by rw [hf0orderG])
  have hPelem : IsElementaryAbelian p P :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hfpow
  have hP0elem : IsElementaryAbelian p P0 :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hf0pow
  have hAelem : IsElementaryAbelian p A := by
    let : IsElementaryAbelian p P := hPelem
    let : IsElementaryAbelian p P0 := hP0elem
    exact IsElementaryAbelian.sup_of_le_centralizer hP0centP
  have hAleFU : A ≤ c.FU := by
    rw [show A = P ⊔ P0 by rfl]
    refine sup_le (hPleF.trans hFleFU) ?_
    intro x hx
    rw [hK0def] at hP0leK0
    exact (hP0leK0 hx).1
  have hAleU : A ≤ c.U := hAleFU.trans (fittingSubgroupOf_le c.U)
  have hprime_le_core : ∀ R : Subgroup G, R ≤ c.FU → Nat.card R = p →
      R ≤ (pCore p c.U).map c.U.subtype := by
    intro R hRleFU hRcard
    have hRleU : R ≤ c.U := hRleFU.trans (fittingSubgroupOf_le c.U)
    let R' : Subgroup c.U := R.subgroupOf c.U
    have hRcard' : Nat.card R' = p :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleU).toEquiv).trans hRcard
    have hR'p : IsPGroup p R' := by
      refine IsPGroup.of_card (n := 1) ?_
      simpa [pow_one] using hRcard'
    have hR'leF : R' ≤ fittingSubgroup c.U := by
      intro x hx
      have hxFU : (x : G) ∈ c.FU := hRleFU hx
      rcases Subgroup.mem_map.mp hxFU with ⟨y, hy, hxy⟩
      have hyx : y = x := Subtype.ext hxy
      rwa [hyx] at hy
    have hcore : R' ⊓ fittingSubgroup c.U ≤ pCore p c.U :=
      pSubgroup_inf_normal_nilpotent_le_pCore
        R' (fittingSubgroup c.U) p hp hR'p (by infer_instance) (by infer_instance)
    intro x hx
    let xU : c.U := ⟨x, hRleU hx⟩
    have hxR' : xU ∈ R' := Subgroup.mem_subgroupOf.mpr hx
    have hxcore : xU ∈ pCore p c.U := hcore ⟨hxR', hR'leF hxR'⟩
    exact Subgroup.mem_map.mpr ⟨xU, hxcore, rfl⟩
  have hPleCore : P ≤ (pCore p c.U).map c.U.subtype :=
    hprime_le_core P (hPleF.trans hFleFU) hPcard
  have hP0leCore : P0 ≤ (pCore p c.U).map c.U.subtype := by
    apply hprime_le_core P0
    · intro x hx
      rw [hK0def] at hP0leK0
      exact (hP0leK0 hx).1
    · exact hP0card
  have hAleCore : A ≤ (pCore p c.U).map c.U.subtype := by
    rw [show A = P ⊔ P0 by rfl]
    exact sup_le hPleCore hP0leCore
  let Op : Subgroup c.U := pCore p c.U
  have hAUleOp : A.subgroupOf c.U ≤ Op := by
    intro x hx
    have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
    rcases Subgroup.mem_map.mp (hAleCore hxA) with ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    subst y
    exact hy
  have hAnc : ¬ IsCyclic A := by
    let : IsElementaryAbelian p A := hAelem
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hAcard
  have hOpnc : ¬ IsCyclic Op := by
    intro hOpcyc
    let : IsCyclic Op := hOpcyc
    have hAUcyc : IsCyclic (A.subgroupOf c.U) :=
      Subgroup.isCyclic_of_le hAUleOp
    exact hAnc ((Subgroup.subgroupOfEquivOfLe hAleU).isCyclic.mp hAUcyc)
  let : Fact (IsPGroup p Op) := ⟨pCore_isPGroup (G := c.U) (p := p)⟩
  let Z2 : Subgroup Op := Subgroup.upperCentralSeries Op 2
  let Om : Subgroup Z2 := omega₁ (G := Z2) (p := p)
  let Q0 : Subgroup Op := z2OmegaCandidate (G := Op) p
  let Q : Subgroup c.U := Q0.map Op.subtype
  obtain ⟨hOmnc, hOmexp⟩ := lemma_4_5_c (R := Op) (p := p) hpne2 hOpnc
  let eOmQ0 : Om ≃* Q0 :=
    Subgroup.equivMapOfInjective Om Z2.subtype Z2.subtype_injective
  let eQ0Q : Q0 ≃* Q :=
    Subgroup.equivMapOfInjective Q0 Op.subtype Op.subtype_injective
  have hQnc : ¬ IsCyclic Q := by
    intro hQcyc
    exact hOmnc (eOmQ0.isCyclic.mpr (eQ0Q.isCyclic.mpr hQcyc))
  have hQexp : Monoid.exponent Q = p := by
    calc
      Monoid.exponent Q = Monoid.exponent Q0 :=
        (Monoid.exponent_eq_of_mulEquiv eQ0Q).symm
      _ = Monoid.exponent Om :=
        (Monoid.exponent_eq_of_mulEquiv eOmQ0).symm
      _ = p := hOmexp
  have hQleZ2 : Q ≤ (Subgroup.upperCentralSeries Op 2).map Op.subtype := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨y, z2OmegaCandidate_le_upperCentralSeries_two (G := Op) (p := p) hy, rfl⟩
  have hQchar : Q.Characteristic := by
    let : Op.Characteristic := by
      dsimp [Op]
      infer_instance
    let : Q0.Characteristic := by
      simpa [Q0] using z2OmegaCandidate_characteristic (G := Op) (p := p)
    exact characteristic_map_subtype_of_characteristic Op Q0
  let od : SecondCaseLinearOmegaData c w d :=
    { p := p
      hp_prime := hp
      K := Kinv
      B := B
      F := F
      s := s
      s_involution := hsIG
      s_mem_H := hsH
      K_inverted := hKinv
      B_fixed := hBfixed
      U_inter_M_eq := hjoinX
      K_cyclic := hKcyc
      K_le_E := hKleE
      K0 := K0
      K0_eq := by simpa [CentralizerSetup.FU] using hK0def
      F_fixed := by simpa [CentralizerSetup.FU] using hFfixed
      FU_inter_M_eq := by simpa [CentralizerSetup.FU] using hjoinY
      F_normal_M := hFnormalM'
      F_centralizes_E := hFcentE
      F_cyclic := hFcyc
      F_normalizer := hNF
      F_TI := hFTI
      F_card_dvd_K0 := hFcarddvd
      P := P
      P_le_F := hPleF
      P_card := hPcard
      P0 := P0
      P0_le_K0 := hP0leK0
      P0_card := hP0card
      A := A
      A_eq := rfl
      A_card := hAcard
      A_elem_abelian := hAelem
      A_le_FU := hAleFU
      Q := Q
      Q_le_upperCentralSeries_two := by simpa [Op] using hQleZ2
      Q_not_cyclic := hQnc
      Q_exponent := hQexp
      Q_characteristic := hQchar }
  have hfull := full_fixed_subgroups_of_nilpotent_normalizer_eq
    c.U c.FU w.M od.F od.B (od.s : G)
      (fittingSubgroupOf_isNilpotent c.U)
      (fittingSubgroupOf_isNormalIn c.U)
      od.F_fixed od.B_fixed od.F_normalizer
  have hF_eq : od.F = c.FU ⊓ Subgroup.centralizer
      (((SE0 : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G) := by
    apply le_antisymm
    · intro x hx
      refine ⟨?_, ?_⟩
      · rw [hfull.1] at hx
        exact hx.1
      · change x ∈ Subgroup.centralizer
          (((SE0 : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyE : y ∈ d.E :=
          Subgroup.map_subtype_le (SE0 : Subgroup d.E) hy
        exact (Subgroup.mem_centralizer_iff.mp
          (od.F_centralizes_E hx)) y hyE
    · intro x hx
      rw [hfull.1]
      refine ⟨hx.1, ?_⟩
      change x ∈ Subgroup.centralizer ({(od.s : G)} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hys : y = (od.s : G) := by simpa using hy
      subst y
      exact (Subgroup.mem_centralizer_iff.mp hx.2) (od.s : G)
        (Subgroup.mem_map.mpr ⟨od.s, hsSE, rfl⟩)
  have hB_centSE_od : od.B ≤ Subgroup.centralizer
      (((SE0 : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G) := by
    change B ≤ Subgroup.centralizer
      (((SE0 : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G)
    exact hBcentSE
  have hK_normSE_od : ((SE0 : Subgroup d.E).map d.E.subtype) ≤
      Subgroup.normalizer (od.K : Set G) := by
    change ((SE0 : Subgroup d.E).map d.E.subtype) ≤
      Subgroup.normalizer (Kinv : Set G)
    exact hKnormSE
  have hXodd : Odd (Nat.card (↥(c.U ⊓ w.M))) := by
    exact Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
  have hsX : ∀ x : G, x ∈ c.U ⊓ w.M →
      (s : G) * x * (s : G)⁻¹ ∈ c.U ⊓ w.M := by
    intro x hx
    refine ⟨(centralizerSetup_U_isNormalIn_H c).2
      (s : G) hsH x hx.1, ?_⟩
    have hsM : (s : G) ∈ w.M := d.E_component.1 s.2
    exact w.M.mul_mem (w.M.mul_mem hsM hx.2) (w.M.inv_mem hsM)
  have hsSEmap : (s : G) ∈
      (SE0 : Subgroup d.E).map d.E.subtype :=
    Subgroup.mem_map.mpr ⟨s, hsSE, rfl⟩
  have hK_comm : Kinv = ⁅(SE0 : Subgroup d.E).map d.E.subtype,
      c.U ⊓ w.M⁆ := by
    exact secondCase_linear_K_eq_componentSylow_commutator
      (X := c.U ⊓ w.M) (K := Kinv) (B := B)
      (A := (SE0 : Subgroup d.E).map d.E.subtype) (s := (s : G))
      hsIG hXodd hsX hKinv hsSEmap hKnormSE hBcentSE hjoinX
  exact ⟨od, hsSE, hsS, hsS0, hF_eq, hB_centSE_od, hK_normSE_od,
    hK_comm⟩

end CFSG.GorensteinWalter
