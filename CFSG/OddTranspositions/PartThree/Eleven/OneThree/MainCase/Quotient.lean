module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Coset
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.TheoremTwo
public import CFSG.OddTranspositions.HalphaQuotient
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Center
import CFSG.OddTranspositions.PartThree.SixThreeGlobal
import CFSG.OddTranspositions.PartFour.Fourteen.Steps
import CFSG.OddTranspositions.SevenFourEight.ImageConnectedThree
import CFSG.LocalAnalysis.EvenSporadicStandard.SolvableRadical
import CFSG.GroupTheory.ABGLocalTools.PStabilityRelative
import CFSG.GroupTheory.PCore.TwoOddCoreSolvable
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.PCore
import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
import CFSG.OddTranspositions.TheoremTwo.PropFourSeven.CaseBStep
import CFSG.Timmesfeld.Bridge.OddLocalRootCore
import CFSG.Timmesfeld.Exceptional.TwoLines
import CFSG.OddTranspositions.PartThree.Nine.ThreeSplit
import CFSG.Mathlib.GroupTheory.MulConjMemNormal
import CFSG.CGT.T75E.Lemma26
import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
import CFSG.CGT.Timmesfeld75.Sec4Three
import CFSG.CGT.Timmesfeld75.Sec5FiveEng
import CFSG.CGT.Timmesfeld75.Step511Card
import CFSG.CGT.Timmesfeld75.Step57Reduction
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.Uniqueness.Bender.OddCentralizer
import CFSG.GH74.Uniqueness.Bender.Unitary
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
import CFSG.LocalAnalysis.WeakClosure81.SevenFour
import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
import CFSG.OddTranspositions.AlmostSimple
import CFSG.OddTranspositions.Disconnected
import CFSG.OddTranspositions.PartFour.Statements
import CFSG.OddTranspositions.TheoremTwo.ImageConnected
import CFSG.OddTranspositions.WreathQuotient
import CFSG.RankThree.GF2n.Tim79aSec2
import CFSG.RankThree.GF2n.Tim79aSec23Inputs
import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace MainHyp

variable {hC : HypothesisC D}

private theorem threeTransp_imageClass_of_oddCore
    (h1 : ∀ d ∈ DstarH hC, ∀ e ∈ DstarH hC,
      orderOf (QuotientGroup.mk' (CFSG.oddCore (Halpha D hC.alpha)) d *
        QuotientGroup.mk' (CFSG.oddCore (Halpha D hC.alpha)) e) ∈ ({1, 2, 3} : Set ℕ)) :
    ∀ d ∈ imageClass hC, ∀ e ∈ imageClass hC,
      orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
  intro d hd e he
  obtain ⟨x, hx, rfl⟩ := hd
  obtain ⟨y, hy, rfl⟩ := he
  let O := CFSG.oddCore (Halpha D hC.alpha)
  let M := CFSG.solvableRadical (Halpha D hC.alpha)
  have hOM : O ≤ M := CFSG.oddCore_le_solvableRadical _
  let φ : Halpha D hC.alpha ⧸ O →* Halpha D hC.alpha ⧸ M :=
    QuotientGroup.lift O (QuotientGroup.mk' M)
      (by simpa [QuotientGroup.ker_mk'] using hOM)
  have hdvd : orderOf (QuotientGroup.mk' M x * QuotientGroup.mk' M y) ∣
      orderOf (QuotientGroup.mk' O x * QuotientGroup.mk' O y) := by
    have h := orderOf_map_dvd φ (QuotientGroup.mk' O x * QuotientGroup.mk' O y)
    rwa [map_mul, show φ (QuotientGroup.mk' O x) = QuotientGroup.mk' M x from rfl,
      show φ (QuotientGroup.mk' O y) = QuotientGroup.mk' M y from rfl] at h
  show orderOf (QuotientGroup.mk' M x * QuotientGroup.mk' M y) ∈ ({1, 2, 3} : Set ℕ)
  rcases h1 x hx y hy with h | h | h <;> rw [h] at hdvd
  · rw [Nat.dvd_one.mp hdvd]; simp
  · rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h' <;> rw [h'] <;> simp
  · rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h' <;> rw [h'] <;> simp

private theorem isSolvable_quotient_of_closure_singleton {H : Type} [Group H] {K : Subgroup H}
    [K.Normal] {c : H ⧸ K}
    (hgen : Subgroup.closure ({c} : Set (H ⧸ K)) = ⊤) : Group.IsSolvable (H ⧸ K) :=
  have : IsCyclic (H ⧸ K) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨c, by rw [Subgroup.zpowers_eq_closure, hgen]⟩
  inferInstance

private theorem mk_mul_self_eq_one_of_center_twoOddCore (hC : HypothesisC D)
    {m X Y : Halpha D hC.alpha}
    (hmK : QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m ∈
      Subgroup.center (Halpha D hC.alpha ⧸ EightOne.twoOddCore (Halpha D hC.alpha)))
    (hYmX : Y = m * X) (hX2 : X * X = 1) (hY2 : Y * Y = 1) :
    QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m *
      QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m = 1 := by
  let π : Halpha D hC.alpha →*
      (Halpha D hC.alpha ⧸ EightOne.twoOddCore (Halpha D hC.alpha)) :=
    QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha))
  have hcomm : Commute (π m) (π X) := (Subgroup.mem_center_iff.mp hmK (π X)).symm
  have hYm : π Y = π m * π X := by rw [hYmX, map_mul]
  have hXπ2 : π X * π X = 1 := by rw [← map_mul, hX2, map_one]
  have hYπ2 : π Y * π Y = 1 := by rw [← map_mul, hY2, map_one]
  have h1 : (π m * π X) * (π m * π X) = (π m * π m) * (π X * π X) :=
    hcomm.symm.mul_mul_mul_comm (π m) (π X)
  rw [← hYm, hYπ2, hXπ2, mul_one] at h1
  exact h1.symm


theorem not_threeTransp_imageClass (h : MainHyp hC) :
    ¬ ∀ d ∈ imageClass hC, ∀ e ∈ imageClass hC, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) :=
  fun h3 => h.not_localSecond (localSecond_of_threeTransp_imageClass hC h3)

theorem exists_hypothesisC_imageClass (h : MainHyp hC) (hconn : ¬ Disconnected (imageClass hC))
    {c : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hc : c ∈ imageClass hC) : ∃ hY : HypothesisC (imageClass hC), hY.d = c := by
  classical
  have hne : (CFSG.Timmesfeld.Bridge.commSet (imageClass hC) c).Nonempty := by
    by_contra hempty
    have hsub : imageClass hC ⊆ ({c} : Set _) := by
      intro z hz
      have hclosed : ∀ y ∈ ({c} : Set _), ∀ w ∈ imageClass hC, Commute y w →
          w ∈ ({c} : Set _) := by
        intro y hy w hw hyw
        rw [Set.mem_singleton_iff] at hy ⊢
        subst hy
        by_contra hwc
        exact hempty ⟨w, hw, hyw.symm, hwc⟩
      exact mem_of_reach hclosed (by rw [Set.mem_singleton_iff])
        (reach_of_not_disconnected hconn hc hz)
    have heq : imageClass hC = {c} := by
      refine Set.Subset.antisymm hsub ?_
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hc
    have hgen : Subgroup.closure ({c} : Set (Halpha D hC.alpha ⧸
        CFSG.solvableRadical (Halpha D hC.alpha))) = ⊤ := by
      rw [← imageClass_gen hC, heq]
    have := isSolvable_quotient_of_closure_singleton hgen
    have : Group.IsSolvable (CFSG.solvableRadical (Halpha D hC.alpha)) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
    exact h.not_isSolvable (Group.isSolvable_of_subgroup_quotient
      (CFSG.solvableRadical (Halpha D hC.alpha)))
  obtain ⟨E, hE⟩ :=
    CFSG.Timmesfeld.Bridge.OddLocal.exists_isMaxOrbit (D := imageClass hC) (d := c) hne
  refine ⟨⟨setup_quotient hC h.not_isSolvable, hconn, c, hc, E, hE⟩, rfl⟩

theorem map_solvableRadical_eq_center_imageClass (h : MainHyp hC)
    (hIH : Theorem11_3Below (Nat.card G)) (hY : HypothesisC (imageClass hC)) :
    (CFSG.solvableRadical (Halpha (imageClass hC) hY.alpha)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (Halpha (imageClass hC) hY.alpha))) =
      Subgroup.center
        (Halpha (imageClass hC) hY.alpha ⧸ CFSG.pCore 2 (Halpha (imageClass hC) hY.alpha)) :=
  hIH (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC) hY
    (natCard_quotient_Halpha_lt hC h.rad) (solvable_normal_eq_bot_imageClass hC)
    (not_threeTransp_imageClass h)

private theorem solvableRadical_map_oddCore_le_center (h : MainHyp hC) :
    (CFSG.solvableRadical (Halpha D hC.alpha)).map
        (QuotientGroup.mk' (CFSG.oddCore (Halpha D hC.alpha))) ≤
      Subgroup.center (Halpha D hC.alpha ⧸ CFSG.oddCore (Halpha D hC.alpha)) := by
  rcases sixThree (Nine.setup_DstarH hC) with h1 | h2 | h3
  · exact absurd (threeTransp_imageClass_of_oddCore h1) (not_threeTransp_imageClass h)
  · exact h2
  · exact (Subgroup.map_mono (otg2_solvableRadical_le_center h.pCore_le_center h3)).trans
      (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _))

theorem mem_twoOddCore_of_mem_solvableRadical (h : MainHyp hC) {x : Halpha D hC.alpha}
    (hx : x ∈ CFSG.solvableRadical (Halpha D hC.alpha)) (hodd : Odd (orderOf x)) :
    x ∈ EightOne.twoOddCore (Halpha D hC.alpha) := by
  let H := Halpha D hC.alpha
  let O := CFSG.oddCore H
  let π : H →* H ⧸ O := QuotientGroup.mk' O
  have hcent : (CFSG.solvableRadical H).map π ≤ Subgroup.center (H ⧸ O) :=
    solvableRadical_map_oddCore_le_center h
  have hxcen : π x ∈ Subgroup.center (H ⧸ O) :=
    hcent (Subgroup.mem_map_of_mem π hx)
  have hoddπ : Odd (orderOf (π x)) := hodd.of_dvd_nat (orderOf_map_dvd π x)
  have hx1 : π x = 1 := by
    have hmem := CFSG.OddTranspositions.PartThree.Nine.mem_oddCore_of_mem_center hxcen hoddπ
    rwa [CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot, Subgroup.mem_bot] at hmem
  have hxO : x ∈ O := (QuotientGroup.eq_one_iff x).mp hx1
  exact oddCore_le_twoOddCore H hxO

private theorem solvableRadical_map_twoOddCore_le_center (h : MainHyp hC) :
    (CFSG.solvableRadical (Halpha D hC.alpha)).map
        (QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha))) ≤
      Subgroup.center (Halpha D hC.alpha ⧸ EightOne.twoOddCore (Halpha D hC.alpha)) := by
  let H := Halpha D hC.alpha
  let K := EightOne.twoOddCore H
  let O := CFSG.oddCore H
  let ρ : H ⧸ O →* H ⧸ K := QuotientGroup.lift O (QuotientGroup.mk' K)
    (by simpa [QuotientGroup.ker_mk'] using oddCore_le_twoOddCore H)
  have hMOK : (CFSG.solvableRadical H).map (QuotientGroup.mk' K) =
      ((CFSG.solvableRadical H).map (QuotientGroup.mk' O)).map ρ := by
    rw [Subgroup.map_map]
    rfl
  have hmap := Subgroup.map_mono (f := ρ) (solvableRadical_map_oddCore_le_center h)
  have hsurj : Function.Surjective ρ :=
    QuotientGroup.lift_surjective_of_surjective O (QuotientGroup.mk' K)
      (QuotientGroup.mk'_surjective K) _
  have hcent := Subgroup.map_center_le_center (f := ρ) hsurj
  rw [hMOK]
  exact hmap.trans hcent

private theorem exists_not_commute_mk_twoOddCore (h : MainHyp hC)
    {x : Halpha D hC.alpha} (hx : x ∈ DstarH hC) :
    ∃ d ∈ DstarH hC,
      ¬ Commute (QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) x)
        (QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) d) := by
  classical
  let H := Halpha D hC.alpha
  let K := EightOne.twoOddCore H
  let π : H →* H ⧸ K := QuotientGroup.mk' K
  by_contra hno
  push Not at hno
  have hcentral : π x ∈ Subgroup.center (H ⧸ K) :=
    CFSG.Timmesfeld.Bridge.OddLocal.mem_center_of_commute_gen
      (CFSG.OddTranspositions.image_closure_eq_top_quotient K (DstarH_closure_eq_top hC))
      (by rintro _ ⟨d, hd, rfl⟩; exact hno d hd)
  have hd_eq : ∀ d ∈ DstarH hC, π d = π x := by
    intro d hd
    obtain ⟨g, hg⟩ := DstarH_transitive hC hx hd
    have hcg : Commute (π g) (π x) := Subgroup.mem_center_iff.mp hcentral (π g)
    rw [← hg, map_mul, map_mul, map_inv, hcg.eq]
    group
  have himage : π '' DstarH hC = {π x} := by
    ext z
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact Set.mem_singleton_iff.mpr (hd_eq d hd)
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      exact ⟨x, hx, hz.symm⟩
  have hgen : Subgroup.closure ({π x} : Set (H ⧸ K)) = ⊤ := by
    rw [← CFSG.OddTranspositions.image_closure_eq_top_quotient K (DstarH_closure_eq_top hC),
      himage]
  have : Group.IsSolvable (H ⧸ K) := isSolvable_quotient_of_closure_singleton hgen
  have : Group.IsSolvable K := CFSG.GroupTheory.isSolvable_comap_oddCore_pCore_two _
  exact h.not_isSolvable (Group.isSolvable_of_subgroup_quotient K)

private theorem exists_order_two_mul_of_center_twoOddCore (h : MainHyp hC)
    {m X : Halpha D hC.alpha}
    (hmK : QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m ∈
      Subgroup.center (Halpha D hC.alpha ⧸ EightOne.twoOddCore (Halpha D hC.alpha)))
    (hm2 : QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m *
      QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m = 1)
    (hm1 : QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m ≠ 1)
    (hxX : X ∈ DstarH hC) :
    ∃ d ∈ DstarH hC, 1 < orderOf (QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) X *
        QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) d) ∧
      orderOf (QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) (m * X) *
          QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) d) =
        2 * orderOf (QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) X *
          QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) d) := by
  let H := Halpha D hC.alpha
  let K := EightOne.twoOddCore H
  let π : H →* H ⧸ K := QuotientGroup.mk' K
  have hxD' : (X : G) ∈ D :=
    DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hxX)
  obtain ⟨d, hd, hnc⟩ := exists_not_commute_mk_twoOddCore h hxX
  have hdD : (d : G) ∈ D := DalphaStar_subset hC.isBlock_alpha hd
  have hncH : ¬ Commute X d := fun hc => hnc (hc.map π)
  have hoddG : Odd (orderOf ((X : G) * (d : G))) :=
    hC.setup.oddT.odd_of_not_commute hxD' hdD
      (fun hc => hncH (Subtype.ext hc.eq))
  have hXdvd : orderOf (π X * π d) ∣ orderOf ((X : G) * (d : G)) := by
    have h1 := orderOf_map_dvd π (X * d)
    rw [map_mul] at h1
    rwa [← Subgroup.orderOf_coe] at h1
  have hoddXd : Odd (orderOf (π X * π d)) := hoddG.of_dvd_nat hXdvd
  have hgt1 : 1 < orderOf (π X * π d) :=
    Nat.lt_of_le_of_ne (Nat.succ_le_iff.mpr (orderOf_pos _))
      (Ne.symm (CFSG.Timmesfeld.Moufang.TwoLines.orderOf_ne_one_of_not_commute hnc))
  have hcomm2 : Commute (π m) (π X * π d) :=
    (Subgroup.mem_center_iff.mp hmK (π X * π d)).symm
  have hmord : orderOf (π m) = 2 :=
    orderOf_eq_prime (p := 2) (hp := ⟨Nat.prime_two⟩) (by rwa [pow_two]) hm1
  have hcop : Nat.Coprime (orderOf (π m)) (orderOf (π X * π d)) := by
    rw [hmord]
    exact hoddXd.coprime_two_left
  have hYdeq : π (m * X) * π d = π m * (π X * π d) := by
    rw [map_mul]
    group
  have hord : orderOf (π (m * X) * π d) = 2 * orderOf (π X * π d) := by
    rw [hYdeq, hcomm2.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hmord]
  exact ⟨d, hd, hgt1, hord⟩

private theorem false_of_center_mul_twoOddCore (h : MainHyp hC) {x y : G}
    (hx : x ∈ DalphaStar D hC.alpha) (hy : y ∈ D) {m : Halpha D hC.alpha}
    (hmK : QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m ∈
      Subgroup.center (Halpha D hC.alpha ⧸ EightOne.twoOddCore (Halpha D hC.alpha)))
    (hm2 : QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m *
      QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m = 1)
    (hm1 : QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m ≠ 1)
    (hym : y = (m : G) * x) : False := by
  let H := Halpha D hC.alpha
  let K := EightOne.twoOddCore H
  let π : H →* H ⧸ K := QuotientGroup.mk' K
  have hxH : x ∈ H := Subgroup.subset_closure hx
  have hyH : y ∈ H := by rw [hym]; exact H.mul_mem m.2 hxH
  let X : H := ⟨x, hxH⟩
  let Y : H := ⟨y, hyH⟩
  have hYmX : Y = m * X := Subtype.ext (by simpa [X, Y, Subgroup.coe_mul] using hym)
  obtain ⟨d, hd, hgt1, hord⟩ := exists_order_two_mul_of_center_twoOddCore h hmK hm2 hm1
    (show X ∈ DstarH hC from hx)
  have hgt1' : 1 < orderOf (π X * π d) := hgt1
  have hdD : (d : G) ∈ D := DalphaStar_subset hC.isBlock_alpha hd
  have hordY : orderOf (π Y * π d) = 2 * orderOf (π X * π d) := by
    rw [← hYmX] at hord
    exact hord
  have hdvd : orderOf (π Y * π d) ∣ orderOf (y * (d : G)) := by
    have h1 := orderOf_map_dvd π (Y * d)
    rw [map_mul] at h1
    rwa [← Subgroup.orderOf_coe] at h1
  rcases hC.setup.oddT.2 y hy (d : G) hdD with h2 | hoddyd
  · have hdiv2 : orderOf (π Y * π d) ∣ 2 := hdvd.trans h2
    rw [hordY] at hdiv2
    have hle : 2 * orderOf (π X * π d) ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv2
    omega
  · have hoddπY : Odd (orderOf (π Y * π d)) := hoddyd.of_dvd_nat hdvd
    rw [hordY] at hoddπY
    obtain ⟨k, hk⟩ := hoddπY
    omega

private theorem mk_eq_one_of_mem_solvableRadical (h : MainHyp hC) {x y : G}
    (hx : x ∈ DalphaStar D hC.alpha) (hy : y ∈ D) {m : Halpha D hC.alpha}
    (hm : m ∈ CFSG.solvableRadical (Halpha D hC.alpha)) (hym : y = (m : G) * x) :
    QuotientGroup.mk' (EightOne.twoOddCore (Halpha D hC.alpha)) m = 1 := by
  classical
  let H := Halpha D hC.alpha
  let K := EightOne.twoOddCore H
  let π : H →* H ⧸ K := QuotientGroup.mk' K
  have hxH : x ∈ H := Subgroup.subset_closure hx
  have hyH : y ∈ H := by rw [hym]; exact H.mul_mem m.2 hxH
  let X : H := ⟨x, hxH⟩
  let Y : H := ⟨y, hyH⟩
  have hYmX : Y = m * X := Subtype.ext (by simpa [X, Y, Subgroup.coe_mul] using hym)
  have hX2 : X * X = 1 := by
    apply Subtype.ext
    simpa [X, Subgroup.coe_mul] using hC.setup.oddT.mul_self_eq_one
      (DalphaStar_subset hC.isBlock_alpha hx)
  have hY2 : Y * Y = 1 := by
    apply Subtype.ext
    simpa [Y, Subgroup.coe_mul] using hC.setup.oddT.mul_self_eq_one hy
  have hmK : π m ∈ Subgroup.center (H ⧸ K) :=
    (solvableRadical_map_twoOddCore_le_center h) (Subgroup.mem_map_of_mem π hm)
  have hm2 : π m * π m = 1 :=
    mk_mul_self_eq_one_of_center_twoOddCore hC hmK hYmX hX2 hY2
  by_cases hm1 : π m = 1
  · exact hm1
  · exact (false_of_center_mul_twoOddCore h hx hy hmK hm2 hm1 hym).elim

theorem exists_twoOddCore_conj_eq_of_mem_solvableRadical (h : MainHyp hC) {x y : G}
    (hx : x ∈ DalphaStar D hC.alpha) (hy : y ∈ D) {m : Halpha D hC.alpha}
    (hm : m ∈ CFSG.solvableRadical (Halpha D hC.alpha)) (hym : y = (m : G) * x) :
    ∃ l ∈ EightOne.twoOddCore (Halpha D hC.alpha), (l : G) * x * (l : G)⁻¹ = y := by
  let K := EightOne.twoOddCore (Halpha D hC.alpha)
  have hm1 : QuotientGroup.mk' K m = 1 := mk_eq_one_of_mem_solvableRadical h hx hy hm hym
  exact exists_twoOddCore_conj_eq h hx hy ((QuotientGroup.eq_one_iff m).mp hm1) hym

private theorem exists_twoOddCore_conj_eq_of_mk_eq (h : MainHyp hC) {δ ε : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha)
    {a c : Halpha D hC.alpha} (ha : (a : G) ∈ δ) (hc : (c : G) ∈ ε)
    (heq : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) :
    ∃ l ∈ EightOne.twoOddCore (Halpha D hC.alpha), l * a * l⁻¹ = c := by
  let H := Halpha D hC.alpha
  let M := CFSG.solvableRadical H
  let K := EightOne.twoOddCore H
  have haStar : (a : G) ∈ DalphaStar D hC.alpha := subset_DalphaStar hδ ha
  have hcD : (c : G) ∈ D := (mem_Dalpha_iff.mp hε).2.1 hc
  have hm : c * a⁻¹ ∈ M := by
    have h1 : QuotientGroup.mk' M (c * a⁻¹) = 1 := by
      rw [map_mul, map_inv, ← heq, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (c * a⁻¹)).mp h1
  have hym : (c : G) = ((c * a⁻¹ : H) : G) * (a : G) := by
    simp [Subgroup.coe_mul]
  obtain ⟨l, hlK, hla⟩ :=
    exists_twoOddCore_conj_eq_of_mem_solvableRadical h haStar hcD hm hym
  exact ⟨l, hlK, Subtype.ext (by simpa using hla)⟩

private theorem exists_pCore_conj_eq_of_twoOddCore_conj (h : MainHyp hC) {δ ε : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha) (hεδ : ε ∈ Dalpha D δ)
    {a c : Halpha D hC.alpha} (ha : (a : G) ∈ δ) (hc : (c : G) ∈ ε)
    {l : Halpha D hC.alpha} (hlK : l ∈ EightOne.twoOddCore (Halpha D hC.alpha))
    (hlac : l * a * l⁻¹ = c) :
    ∃ r ∈ CFSG.pCore 2 (Halpha D hC.alpha),
      (r : G) * (a : G) * (r : G)⁻¹ = (c : G) := by
  let H := Halpha D hC.alpha
  let K := EightOne.twoOddCore H
  have haStar : (a : G) ∈ DalphaStar D hC.alpha := subset_DalphaStar hδ ha
  have hcD : (c : G) ∈ D := (mem_Dalpha_iff.mp hε).2.1 hc
  have hacomm : Commute a c :=
    Subtype.ext ((mem_Dalpha_iff.mp hεδ).2.2.2 (a : G) ha (c : G) hc).eq
  have ha2 : a * a = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_mul] using hC.setup.oddT.mul_self_eq_one
      (DalphaStar_subset hC.isBlock_alpha haStar)
  have hacK : a * c ∈ K := by
    rw [show c = l * a * l⁻¹ from hlac.symm]
    exact CFSG.GroupTheory.mul_mul_conj_mem_of_normal hlK ha2
  have hq : a * c ∈ CFSG.pCore 2 H :=
    mul_mem_pCore_of_mul_mem_twoOddCore hC (hδ.2.1 ha) hcD
      (hacomm.map H.subtype) hacK
  have hca : (a * c) * a = c := by
    calc (a * c) * a = a * (c * a) := by group
      _ = a * (a * c) := by rw [hacomm.eq]
      _ = (a * a) * c := by group
      _ = c := by rw [ha2, one_mul]
  have hwq : (c : G) = ((a * c : H) : G) * (a : G) :=
    (congrArg Subtype.val hca).symm
  exact exists_pCore_conj_eq h haStar hcD hq hwq

theorem eq_of_pCore_conj_eq (h : MainHyp hC) {a c : Halpha D hC.alpha}
    {r : Halpha D hC.alpha} (hrQ : r ∈ CFSG.pCore 2 (Halpha D hC.alpha))
    (hra : (r : G) * (a : G) * (r : G)⁻¹ = (c : G)) : (c : G) = (a : G) := by
  have hrcomm : (r : G) * (a : G) = (a : G) * (r : G) := by
    simpa using congrArg Subtype.val
      (Subgroup.mem_center_iff.mp (h.pCore_le_center hrQ) a).symm
  rw [← hra, hrcomm]
  group

theorem mk_ne_mk_of_mem_Dalpha (h : MainHyp hC) {δ ε : Set G} (hδ : δ ∈ Dalpha D hC.alpha)
    (hε : ε ∈ Dalpha D hC.alpha) (hεδ : ε ∈ Dalpha D δ) {a c : Halpha D hC.alpha}
    (ha : (a : G) ∈ δ) (hc : (c : G) ∈ ε) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c := by
  intro heq
  obtain ⟨l, hlK, hlac⟩ := exists_twoOddCore_conj_eq_of_mk_eq h hδ hε ha hc heq
  obtain ⟨r, hrQ, hra⟩ := exists_pCore_conj_eq_of_twoOddCore_conj h hδ hε hεδ ha hc hlK hlac
  exact CFSG.OddTranspositions.PropFourSeven.ne_of_mem_of_ne_block hC.isBlock_alpha hδ.1 hε.1
    (Ne.symm (mem_Dalpha_iff.mp hεδ).2.2.1) ha hc (eq_of_pCore_conj_eq h hrQ hra).symm


end MainHyp

end CFSG.OddTranspositions.PartThree.ElevenThree
