module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCPerf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
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
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
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
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDeltaBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.GroupTheory.SteinbergBMTwoPartCommutatorsOdd
public import CFSG.RankThree.PartOne.KC.LinearPrimeFieldActorSolvableCore
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c13bc_barSub_wClos_le {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {S : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hA : ∀ A ∈ E3.gammaSet V D.k D.T, barSub V₀ V h.isElemAbelian A ≤ S) :
    barSub V₀ V h.isElemAbelian (E3.wClos V D.k D.T) ≤ S := by
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hle : E3.wClos V D.k D.T ≤ preBarSub D.M V₀ V h.isElemAbelian S := by
    refine E3.wClos_le_of_forall fun A hAΓ g hg => ?_
    have hgM : g ∈ D.M := D.sylowM.le (hAΓ.1 hg)
    have hgst : g ∈ stabTil V₀ V := hMst hgM
    exact (mem_preBarSub _ _ _ _ _).2
      ⟨hgM, hgst, hA A hAΓ (actTil_mem_barSub V₀ V h.isElemAbelian hg hgst)⟩
  have := barSub_mono V₀ V h.isElemAbelian hle
  rw [barSub_preBarSub] at this
  exact this.trans inf_le_left

theorem s16c13bc_center_map_eq_bot {Γ : Type*} [Group Γ] {L : Subgroup Γ} (f : Γ →* Γ)
    (hf : Function.Injective f) (h : Subgroup.center ↥L = ⊥) :
    Subgroup.center ↥(L.map f) = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.1 b.2
  have hac : (⟨a, ha⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro c
    have h1 := Subgroup.mem_center_iff.1 hb ⟨f c, Subgroup.mem_map_of_mem f c.2⟩
    have h2 : f c * f a = f a * f c := by
      have := congrArg Subtype.val h1
      simpa [hab] using this
    apply Subtype.ext
    apply hf
    simpa using h2
  rw [h, Subgroup.mem_bot] at hac
  have ha1 : a = 1 := congrArg Subtype.val hac
  apply Subtype.ext
  rw [← hab, ha1, map_one]
  rfl

private theorem s16c13bc_map_conj_map_conj {T : Type*} [CommGroup T] (A : Subgroup (MulAut T))
    (x y : MulAut T) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      A.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem s16c13bc_map_conj_one {T : Type*} [CommGroup T] (A : Subgroup (MulAut T)) :
    A.map (MulAut.conj (1 : MulAut T)).toMonoidHom = A := by
  ext z
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem s16c13bc_exists_other_conj (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hH : Hyp151 D V₀ V L) (hs : s15 D.M V₀ V hV L = 2) :
    ∃ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom ≠ lBar V₀ V hV L ∧
      ∀ b ∈ (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom,
        ∀ w ∈ wTil V₀ V hV L, b w = w := by
  classical
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs
    exact hs
  obtain ⟨g₂, hg₂M, hg₂ne⟩ : ∃ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom ≠ lBar V₀ V hV L := by
    by_contra hcon
    have hsingle : {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV,
          Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = {lBar V₀ V hV L} := by
      ext Y
      constructor
      · rintro ⟨φ, hφM, rfl⟩
        by_contra hne
        exact hcon ⟨φ, hφM, hne⟩
      · rintro rfl
        exact ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩
    rw [hsingle] at hcls
    simp at hcls
  obtain ⟨x, hxM, hxg₂⟩ := (mem_barSub V₀ V hV D.M g₂).1 hg₂M
  have hgne : (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom ≠ lBar V₀ V hV L := by
    intro h
    apply hg₂ne
    have h' := congrArg (fun X : Subgroup (MulAut (Vtil V₀ V hV)) =>
      X.map (MulAut.conj g₂).toMonoidHom) h
    rw [s16c13bc_map_conj_map_conj, mul_inv_cancel, s16c13bc_map_conj_one] at h'
    exact h'.symm
  have hgM : g₂⁻¹ ∈ Mbar D.M V₀ V hV := (Mbar D.M V₀ V hV).inv_mem hg₂M
  have hconjinv : ((MulAut.conj g₂)⁻¹).toMonoidHom =
      (MulAut.conj g₂⁻¹).toMonoidHom := by
    ext z
    simp [MulAut.conj_apply]
  have hbar : barSub V₀ V hV (conjSubgroup L (x : G)) =
      (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV x.2 L, hxg₂]
    exact congrArg (fun f : MulAut (Vtil V₀ V hV) →* MulAut (Vtil V₀ V hV) =>
      (barSub V₀ V hV L).map f) hconjinv
  have hxnbar : (x : G) ∉ nBar D.M V₀ V hV L := by
    intro hx
    rw [s15_Infra_mem_nBar_iff hH.hyp125 hV hxM] at hx
    rw [hbar] at hx
    exact hgne hx
  have hcomm := hH.commute (x : G) hxM hxnbar
  rw [hbar] at hcomm
  refine ⟨g₂⁻¹, hgM, hgne, ?_⟩
  intro b hb w hw
  have hle : wTil V₀ V hV L ≤ fixV ((lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom) :=
    commSub_eq_bot_iff.mp hcomm.2
  exact (mem_fixV.mp (hle hw)) b hb

theorem s16c13bc_case168_9 (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV)
    (hcomm : ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ = ⊥)
    (hΓ : ∀ A ∈ E3.gammaSet V D.k D.T, barSub ⊥ V hV A ≤ stabSub (wTil ⊥ V hV L))
    (h9 : Case168_9 D ⊥ V hV L) : Insp1613U D V := by
  have h : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hH : Hyp151 D ⊥ V L := hc.setting.hyp151
  obtain ⟨⟨e⟩, hL3, hs15, -, hσ⟩ := h9
  have hp7 : (7 : ℕ) ∈ D.sig := by
    rw [hσ]
    exact Set.mem_singleton 7
  have hLc : Subgroup.center ↥(lBar ⊥ V hV L) = ⊥ := center_eq_bot_of_isL3 hL3
  have hLp : _root_.commutator ↥(lBar ⊥ V hV L) = ⊤ := s16c1610_commutator_of_isL3 hL3
  have hLcard : Nat.card ↥(lBar ⊥ V hV L) = 168 := card_eq_of_isL3 hL3
  have hQ : Subgroup.center (↥(lBar ⊥ V hV L) × ↥(lBar ⊥ V hV L)) = ⊥ := by
    rw [Subgroup.center_prod, hLc, Subgroup.bot_prod_bot]
  obtain ⟨Z, -, hZM, hZcard, hZnorm, -⟩ :=
    s16c1610_center_fstar (Mb := Mbar D.M ⊥ V hV) (p := 7) hQ e
  have hW : wTil ⊥ V hV L ≠ ⊥ := fun h0 => hc.ne_bot (s15_Lin_eq_bot_of_commSub_top_eq_bot h0)
  obtain ⟨n, hnW, hn1, hnfix⟩ :=
    s16c13bc_exists_fixed_in D h hW (s16c13bc_barSub_wClos_le h hΓ)
  obtain ⟨g, hgM, -, hfix⟩ := s16c13bc_exists_other_conj D hV hH hs15
  set B : Subgroup (MulAut (Vtil ⊥ V hV)) :=
    (lBar ⊥ V hV L).map (MulAut.conj g).toMonoidHom with hB
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hBcard : Nat.card ↥B = 168 := by
    rw [hB, Subgroup.card_map_of_injective hinj, hLcard]
  haveI : Group.IsPerfect ↥(lBar ⊥ V hV L) := Group.isPerfect_def.2 hLp
  have hBp : _root_.commutator ↥B = ⊤ :=
    Group.isPerfect_def.1 (Group.IsPerfect.map (H := lBar ⊥ V hV L) (MulAut.conj g).toMonoidHom)
  have hBc : Subgroup.center ↥B = ⊥ := s16c13bc_center_map_eq_bot _ hinj hLc
  have hBM : B ≤ Mbar D.M ⊥ V hV := by
    rintro _ ⟨a, ha, rfl⟩
    have haM : a ∈ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hH.le ha
    show g * a * g⁻¹ ∈ Mbar D.M ⊥ V hV
    exact (Mbar D.M ⊥ V hV).mul_mem ((Mbar D.M ⊥ V hV).mul_mem hgM haM)
      ((Mbar D.M ⊥ V hV).inv_mem hgM)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 7 (by rw [hBcard]; norm_num)
  have hψo : orderOf (a : MulAut (Vtil ⊥ V hV)) = 7 := by
    rw [Subgroup.orderOf_coe]
    exact ha
  have hψ1 : (a : MulAut (Vtil ⊥ V hV)) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hψo
    omega
  have hψZ : (a : MulAut (Vtil ⊥ V hV)) ∉ Z :=
    s16c13bc_not_mem_of_perfect (by norm_num) hBp hBc hZcard
      (fun m hm x hx => hZnorm m (hBM hm) x hx) a.2 hψ1
  exact s16c13bc_insp_of_normal_prime D h hcomm hp7 hZM hZcard hZnorm hn1 hnfix (hBM a.2) hψo
    hψZ (hfix _ a.2 n hnW)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
