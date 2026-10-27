module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRank
public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.HardMathSupport.Lang.Triality.SylowInnerExt
public import CFSG.GroupTheory.CoprimeCentralizerRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFour
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
public import CFSG.GroupTheory.PCore.Transport
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
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.SectionRank
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise commutatorElement

local notation "pRank" => CFSG.Open.pRank

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_pRank_bar2_add_pRank_centOverO2 {X M : Subgroup G} (hXM : X ≤ M)
    (hMN : M ≤ normalizer (X : Set G)) (hZ : center (Bar2 X) = ⊥)
    (hOut : IsCyclic (Outer (Bar2 X))) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hOp : UC22.F10.OpRes p M = M) :
    pRank p M ≤ pRank p (⊤ : Subgroup (Bar2 X)) + pRank p (F08.CentOverO2 M X) := by
  classical
  have hp1 : 1 < p := hp.one_lt
  let ρ : ↥M →* MulAut (Bar2 X) := (rhoL X).comp (Subgroup.inclusion hMN)
  obtain ⟨E, hEM, hEel, hEcard⟩ := exists_pRank hp1 M
  have hEeq : pRank p E = pRank p M := by
    refine le_antisymm (pRank_mono hp1 hEM) ?_
    exact le_pRank hp1 le_rfl hEel hEcard
  have hmap := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map
    (G := ↥M) (H := MulAut (Bar2 X)) hp ρ (E.subgroupOf M)
  have hsub : pRank p (E.subgroupOf M) = pRank p E := by
    rw [pRank_eq_pRank_top_subgroup (E.subgroupOf M), pRank_eq_pRank_top_subgroup E]
    exact pRank_top_eq_of_mulEquiv hp1 (Subgroup.subgroupOfEquivOfLe hEM)
  have hker : pRank p (E.subgroupOf M ⊓ ρ.ker) ≤ pRank p (F08.CentOverO2 M X) := by
    have hKmap : ((E.subgroupOf M ⊓ ρ.ker).map M.subtype) ≤ F08.CentOverO2 M X := by
      rw [centOverO2_eq_ker_map hMN]
      exact Subgroup.map_mono (inf_le_right : E.subgroupOf M ⊓ ρ.ker ≤ ρ.ker)
    exact (pRank_le_map hp1 M.subtype M.subtype_injective _).trans (pRank_mono hp1 hKmap)
  have himg : pRank p ((E.subgroupOf M).map ρ) ≤ pRank p (⊤ : Subgroup (Bar2 X)) := by
    have hle : (E.subgroupOf M).map ρ ≤
        CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X) := by
      simpa [ρ] using map_rhoL_le_inner_of_isCyclic_outer hMN hOut hp hOp hEM hEel
    have hinner : pRank p (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X)) =
        pRank p (⊤ : Subgroup (Bar2 X)) := by
      have hconj : Function.Injective (MulAut.conj : Bar2 X →* MulAut (Bar2 X)) :=
        CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot hZ
      have hrange : CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X) =
          (⊤ : Subgroup (Bar2 X)).map (MulAut.conj : Bar2 X →* MulAut (Bar2 X)) := by
        rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_map]
      rw [hrange, pRank_eq_pRank_top_subgroup ((⊤ : Subgroup (Bar2 X)).map
        (MulAut.conj : Bar2 X →* MulAut (Bar2 X))),
        pRank_eq_pRank_top_subgroup (⊤ : Subgroup (Bar2 X))]
      exact (pRank_top_eq_of_mulEquiv hp1
        (Subgroup.equivMapOfInjective (⊤ : Subgroup (Bar2 X))
          (MulAut.conj : Bar2 X →* MulAut (Bar2 X)) hconj)).symm
    exact (pRank_mono hp1 hle).trans_eq hinner
  calc
    pRank p M = pRank p (E.subgroupOf M) := (hsub.trans hEeq).symm
    _ ≤ pRank p (E.subgroupOf M ⊓ ρ.ker) + pRank p ((E.subgroupOf M).map ρ) := hmap
    _ ≤ pRank p (F08.CentOverO2 M X) + pRank p (⊤ : Subgroup (Bar2 X)) :=
        add_le_add hker himg
    _ = pRank p (⊤ : Subgroup (Bar2 X)) + pRank p (F08.CentOverO2 M X) := Nat.add_comm _ _

theorem pRank_centOverO2_le_pRank_inf_centralizer {X M R : Subgroup G} (hXM : X ≤ M)
    (hMN : M ≤ normalizer (X : Set G)) {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hRX : R ≤ X) (hRp : IsPGroup r R) :
    pRank p (F08.CentOverO2 M X) ≤ pRank p (M ⊓ centralizer (R : Set G)) := by
  classical
  have hp1 : 1 < p := hp.one_lt
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hO2p : ¬ p ∣ Nat.card (pCoreOf 2 X) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (isPGroup_pCoreOf X) hp hp2
  have hO2r : ¬ r ∣ Nat.card (pCoreOf 2 X) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (isPGroup_pCoreOf X) hr hr2
  obtain ⟨S, hSyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (F08.CentOverO2 M X)
  have hSM : S ≤ M := hSyl.le.trans fun x hx => (mem_centOverO2_iff.mp hx).1
  have hrank : pRank p S = pRank p (F08.CentOverO2 M X) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.pRank_eq_of_isSylowOf hSyl
  have hcomm : ⁅S, R⁆ ≤ pCoreOf 2 X := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    rw [commutatorElement_def]
    exact (mem_centOverO2_iff.mp (hSyl.le hs)).2 t (hRX ht)
  have hle := CFSG.GroupTheory.pRank_le_pRank_inf_centralizer_of_commutator_le
    (p := p) (q := r) (M := M) (N := pCoreOf 2 X) (R := S) (B := R)
    hSM ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXM)
    (hSM.trans (hMN.trans (normalizer_le_normalizer_pCoreOf X)))
    (hRX.trans (hXM.trans (hMN.trans (normalizer_le_normalizer_pCoreOf X))))
    hSyl.isPGroup hRp hO2p hO2r hcomm
  calc
    pRank p (F08.CentOverO2 M X) = pRank p S := hrank.symm
    _ ≤ pRank p (M ⊓ centralizer (R : Set G)) := hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
