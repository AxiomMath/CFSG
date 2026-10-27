module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaE
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
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
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.B15P4 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16h_ncard_conjSetOf_cover_eq_s15
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : Hyp151 D V₀ V L)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hbar : barSub V₀ V hV K = lBar V₀ V hV L) :
    (conjSetOf D.M K).ncard = s15 D.M V₀ V hV L := by
  classical
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hna : ∀ (g : G) (hg : g ∈ D.M),
      ⁅barSub V₀ V hV (K.map (MulAut.conj g).toMonoidHom),
        barSub V₀ V hV (K.map (MulAut.conj g).toMonoidHom)⁆ ≠ ⊥ := by
    intro g hg
    have hg' : g⁻¹ ∈ D.M := D.M.inv_mem hg
    have hgbar : barSub V₀ V hV (K.map (MulAut.conj g).toMonoidHom) =
        (lBar V₀ V hV L).map
          (MulAut.conj (actTil V₀ V hV ⟨g⁻¹, hMs hg'⟩)⁻¹).toMonoidHom := by
      rw [show K.map (MulAut.conj g).toMonoidHom = conjSubgroup K g⁻¹ from by
        rw [conjSubgroup, inv_inv]]
      rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hg') K, hbar]
    rw [hgbar, ← Subgroup.map_commutator]
    change (⁅lBar V₀ V hV L, lBar V₀ V hV L⁆).map _ ≠ ⊥
    rw [perfect_of_isComponentOf hcomp]
    intro hbot
    exact ne_bot_of_isComponentOf hcomp
      ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).1 hbot)
  have hinj : Set.InjOn (fun X : Subgroup G => barSub V₀ V hV X) (conjSetOf D.M K) := by
    intro X hX Y hY hXY
    obtain ⟨g, hg, rfl⟩ := hX
    obtain ⟨k, hk, rfl⟩ := hY
    have hXcal : K.map (MulAut.conj g).toMonoidHom ∈ calC D.M := by
      have hconj := uc22p22u_calC_conj (Subgroup.le_normalizer (H := D.M)) hK
        (D.M.inv_mem hg)
      simpa only [CFSG.Open.uniqueFourConj, inv_inv] using hconj
    have hYcal : K.map (MulAut.conj k).toMonoidHom ∈ calC D.M := by
      have hconj := uc22p22u_calC_conj (Subgroup.le_normalizer (H := D.M)) hK
        (D.M.inv_mem hk)
      simpa only [CFSG.Open.uniqueFourConj, inv_inv] using hconj
    exact s16h_e3_omega_calC_eq_of_barSub_eq h.hyp125 hXcal hYcal hXY (hna g hg)
  have himage : (fun X : Subgroup G => barSub V₀ V hV X) '' conjSetOf D.M K =
      Set.range (fun m : D.M =>
        barSub V₀ V hV (conjSubgroup L (m : G))) := by
    ext Y
    constructor
    · rintro ⟨X, ⟨g, hg, rfl⟩, rfl⟩
      refine ⟨⟨g⁻¹, D.M.inv_mem hg⟩, ?_⟩
      dsimp only
      rw [show K.map (MulAut.conj g).toMonoidHom = conjSubgroup K g⁻¹ from by
        rw [conjSubgroup, inv_inv]]
      rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs (D.M.inv_mem hg)) K, hbar,
        s15_Infra_barSub_conjSubgroup V₀ V hV (hMs (D.M.inv_mem hg)) L]
      rfl
    · rintro ⟨m, rfl⟩
      refine ⟨conjSubgroup K (m : G), ⟨(m : G)⁻¹, D.M.inv_mem m.2, ?_⟩, ?_⟩
      · rw [conjSubgroup]
      · dsimp only
        rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs m.2) K, hbar,
          s15_Infra_barSub_conjSubgroup V₀ V hV (hMs m.2) L]
        rfl
  calc (conjSetOf D.M K).ncard
      = ((fun X : Subgroup G => barSub V₀ V hV X) '' conjSetOf D.M K).ncard :=
        (Set.InjOn.ncard_image hinj).symm
    _ = (Set.range (fun m : D.M =>
          barSub V₀ V hV (conjSubgroup L (m : G)))).ncard := by rw [himage]
    _ = s15 D.M V₀ V hV L := (s15_Core_s15_eq_ncard_range h).symm

theorem s16h_ncard_conjSetOf_cover_eq_two
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : Hyp151 D V₀ V L)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs2 : s15 D.M V₀ V hV L = 2)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hbar : barSub V₀ V hV K = lBar V₀ V hV L) :
    (conjSetOf D.M K).ncard = 2 := by
  rw [s16h_ncard_conjSetOf_cover_eq_s15 h hcomp hK hbar, hs2]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
