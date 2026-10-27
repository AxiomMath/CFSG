module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Order
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Y
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSmall
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_card_v0_le_four (D : Data G) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) :
    Nat.card V₀ ≤ 4 := by
  have hcard : Nat.card V₀ = 2 ^ mSub V₀ :=
    card_eq_two_pow_mSub h.hyp125.pairFacts.elemAbelian₀.isPGroup
  rw [hcard]
  calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h.small
    _ = 4 := by norm_num

theorem c23_exists_noncyclic_in_preBarSub (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_2 D V₀ V hV L ∨ Case167_3 D V₀ V hV L) :
    ∃ (p : ℕ) (E : Subgroup G) (x : G) (B : Subgroup G), p.Prime ∧ 3 ≤ p ∧ p ∈ D.sig ∧
      E ≤ D.M ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ x ∈ D.M ∧
      x ∉ nBar D.M V₀ V hV L ∧ B ≤ E ∧
      B ≤ preBarSub D.M V₀ V hV (barSub V₀ V hV (conjSubgroup L x)) ∧
      IsElemAbelian p B ∧ ¬ IsCyclic ↥B := by
  obtain ⟨p, hp, hp3, hpσ, hpL, hpM⟩ := c23_exists_prime D h1217 hS hc
  have h151 := hS.setting.hyp151
  have hs : s15 D.M V₀ V hV L = 2 := by
    rcases hc with hc | hc
    · exact hc.2.2.1
    · exact hc.2.2.1
  obtain ⟨E, hEM, hEea, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := p) (M := D.M) (k := 3) hp (by
      rw [UC6.groupPRank_eq_pRank]
      exact hSg.three_le p hpσ)
  obtain ⟨x, hxM, hxn⟩ := c23_exists_mem_not_nBar D h151 hV hs
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h151.hyp125.pairFacts.le_normalizer h151.hyp125.pairFacts.le_normalizer₀
  have hx' : x ∈ stabTil V₀ V := hMs hxM
  have hKM : barSub V₀ V hV (conjSubgroup L x) ≤ Mbar D.M V₀ V hV :=
    c23_barSub_conjSubgroup_le_Mbar D h151 hV hxM
  have hpK : p ∣ Nat.card (barSub V₀ V hV (conjSubgroup L x)) := by
    rw [c23_card_barSub_conjSubgroup hV hx' L]
    exact hpL
  have hN := c23_barSub_le_normalizer_conjSubgroup D h151 hV hs hxM hxn hp (by omega)
    hEM hEea.isPGroup
  obtain ⟨B, hBE, hBY, hBel, hBc⟩ :=
    c23_exists_noncyclic_le_preBarSub hV hp hEM hMs hEea hEcard hKM hpK hpM hN
  exact ⟨p, E, x, B, hp, hp3, hpσ, hEM, hEea, hEcard, hxM, hxn, hBE, hBY, hBel, hBc⟩

theorem c23_uniqueMax_of_mem_v0 (D : Data G) (h61 : UC6.R6_1 D) {V₀ : Subgroup G}
    (hV₀ : Nat.card V₀ ≤ 4) (hN : D.M ≤ normalizer (V₀ : Set G)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) (hpσ : p ∈ D.sig) {E : Subgroup G} (hEM : E ≤ D.M) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 3) {w : G} (hw : w ∈ V₀) (hw1 : w ≠ 1) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  let S : Set G := {v | v ∈ V₀ ∧ v ≠ 1}
  have hSfin : S.Finite := Set.toFinite S
  have hS3 : S.ncard ≤ 3 := by
    have hins : insert (1 : G) S ⊆ (V₀ : Set G) := by
      intro v hv
      rw [Set.mem_insert_iff] at hv
      rcases hv with rfl | hv
      · exact V₀.one_mem
      · exact hv.1
    have h1not : (1 : G) ∉ S := by
      intro h
      exact h.2 rfl
    have hcard := Set.ncard_le_ncard hins
    rw [Set.ncard_insert_of_notMem h1not hSfin] at hcard
    have hV₀' : (V₀ : Set G).ncard ≤ 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hV₀
    omega
  have hSw : ∀ e ∈ E, e * w * e⁻¹ ∈ S := by
    intro e he
    refine ⟨?_, ?_⟩
    · exact ((Subgroup.mem_normalizer_iff.1 (hN (hEM he))) w).1 hw
    · intro h
      exact hw1 (by
        calc w = e⁻¹ * (e * w * e⁻¹) * e := by group
          _ = 1 := by rw [h]; group)
  have hnc := c23_not_isCyclic_inf_centralizer hp hp3 hE hEcard hS3 hSw
  have hE' : IsPGroup p ↥(E ⊓ centralizer ({w} : Set G)) :=
    (IsElemAbelian.mono hE inf_le_left).isPGroup
  have hXle : E ⊓ centralizer ({w} : Set G) ≤ D.M := inf_le_left.trans hEM
  exact c23_uniqueMax_of_noncyclic D h61 hpσ hE' hnc (le_inf hXle inf_le_right) inf_le_left

theorem c23_uniqueMax_of_le_cElt (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V) (hV₀ : Nat.card V₀ ≤ 4) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig) {B : Subgroup G} (hB : IsPGroup p B)
    (hBc : ¬ IsCyclic ↥B) {w : G} (hwV : w ∈ V) (hw0 : w ∉ V₀)
    (hBw : B ≤ F11.CElt D.M V₀ w) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have h113 := r113_holds (D := D)
  obtain ⟨n, _hn2, hn⟩ := h113 V₀ V hH hV₀ w hwV hw0
  have hindex : ¬ p ∣ (D.M ⊓ centralizer ({w} : Set G)).relIndex (F11.CElt D.M V₀ w) := by
    intro hdvd
    rw [hn] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  obtain ⟨B', hB'H, hB'p, hB'c⟩ :=
    c23_exists_noncyclic_le_of_not_dvd_relIndex hp hBw hindex hB hBc
  exact c23_uniqueMax_of_noncyclic D h61 hpσ hB'p hB'c hB'H inf_le_left

theorem c23_unique₁ (D : Data G) (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_2 D V₀ V hV L ∨ Case167_3 D V₀ V hV L) :
    ∀ w ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  intro w hw hw1
  have h151 := hS.setting.hyp151
  have h16 := hS.setting.hyp16
  have hs : s15 D.M V₀ V hV L = 2 := by
    rcases hc with hc | hc
    · exact hc.2.2.1
    · exact hc.2.2.1
  obtain ⟨p, E, x, B, hp, hp3, hpσ, hEM, hEel, hEcard, hxM, hxn, hBE, hBY, hBel, hBc⟩ :=
    c23_exists_noncyclic_in_preBarSub D hSg h1217 hS hc
  by_cases h0 : V₀ = ⊥
  · have hcases : ∀ m ∈ D.M, barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L ∨
        barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV (conjSubgroup L x) :=
      fun m hm => c23_barSub_conj_cases D h151 hV hs hxM hxn hm
    have hYw := c23_preBarSub_conj_le_centralizer D h151 hV h0 hxM hxn hcases hw
    have hBle : B ≤ D.M ⊓ centralizer ({w} : Set G) :=
      le_inf (hBE.trans hEM) (hBY.trans hYw)
    exact c23_uniqueMax_of_noncyclic D h61 hpσ hBel.isPGroup hBc hBle inf_le_left
  · have hv1 : v1Sub D.M V₀ V hV L = V₀ := v1Sub_of_ne_bot D.M V₀ V hV L h0
    have hleW : V₀ ≤ wSub V₀ V hV L := s15_Two_le_wSub hV h151.hyp125.pairFacts.le L
    have hsup : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L = wSub V₀ V hV L := by
      rw [hv1]
      exact sup_eq_left.mpr hleW
    have hwW : w ∈ wSub V₀ V hV L := by
      rw [hsup] at hw
      exact hw
    have hV₀ : Nat.card V₀ ≤ 4 := c23_card_v0_le_four D h16
    by_cases hwV₀ : w ∈ V₀
    · exact c23_uniqueMax_of_mem_v0 D h61 hV₀ h151.hyp125.pairFacts.le_normalizer₀
        hp hp3 hpσ hEM hEel hEcard hwV₀ hw1
    · have hwV : w ∈ V := preTil_le V₀ V hV _ hwW
      have hBw : B ≤ F11.CElt D.M V₀ w :=
        hBY.trans (c23_preBarSub_conj_le_cElt D h151 hV hxM hxn hwW)
      exact c23_uniqueMax_of_le_cElt D h61 (Hyp125.hyp11 h127 h151.hyp125)
        hV₀ hp (by omega) hpσ hBel.isPGroup hBc hwV hwV₀ hBw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
