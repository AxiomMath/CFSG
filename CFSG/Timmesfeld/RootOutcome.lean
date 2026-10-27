module

public import CFSG.Timmesfeld.Assembly

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint

namespace Bridge

theorem closures_of_stepsSE_NJ2 (hL : LargeStepSE) (hX : Moufang.ExceptionalGlobalStepNJ2)
    (hconn : ∀ (G : Type) [Group G] (D : Set G), Hyp G D → Moufang.NoPolar D →
      Closure.CommConnected D)
    (hA : ARSInput) {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) :
    RootClosure D ∧ SpecialClosure D ∧ RootMoufang D ∧ ExistsCommSpec D := by
  suffices key : ∀ n : ℕ, ∀ (G : Type) [Group G] (D : Set G), Nat.card G = n → Hyp G D →
      Outcome G ∧ ((∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) →
        RootClosure D ∧ SpecialClosure D ∧ RootMoufang D ∧ ExistsCommSpec D) from
    (key _ G D rfl h).2 hl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ D hn h
    have IH : RootIHStructE G := fun G' _ D' h' hlt => ih _ (hn ▸ hlt) G' D' rfl h'
    refine ⟨?_, hL G D h IH⟩
    by_cases hJ : NativeSporadic.IsSporadic G .J2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ))))))
    · refine outcome_at h (fun hl => ?_)
        (fun hsing hex => hX G D h IH.toStruct.rootIH hsing hex hJ) (hconn G D h) hA
      obtain ⟨hc, hs, hm, _⟩ := hL G D h IH hl
      exact ⟨hc, hs, hm⟩

end Bridge

theorem largeClosures {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) :
    RootClosure D ∧ SpecialClosure D ∧ RootMoufang D := by
  have h := openInputs_holds
  have hT : Moufang.Tim75Thm31 := Bridge.tim75Thm31
  have hK : Bridge.ThirdKindStep :=
    Bridge.RootClosure.thirdKindStep_of_rootThreeL2 Bridge.commonNeighbour hT
      (Bridge.RootClosure.rootThreeL2Stmt_of Bridge.RootClosure.psl2SylowCoordStmt
        Bridge.RootClosure.l2TorusIrredStmt Bridge.RootClosure.naturalComplementStmt)
  obtain ⟨hc, hs, hm, -⟩ := Bridge.closures_of_stepsSE_NJ2
    (Bridge.largeStepSE_of_third hK Bridge.gammaResidualStep
      (Bridge.commLambdaStep_of_nCore (Bridge.nCoreStep_of_nCoreStepLarge Bridge.nCoreStepLarge))
      (Bridge.existsCommSpecStepE_of_thin hT Bridge.nCoreStepLarge
        (Bridge.thinOneOppositeStepE_of_split
          (Bridge.thinManyStepE_of Bridge.rootLinesPowerStep Bridge.rootLinesTorusStep
            (Bridge.thinGateManyStep_of
              (Bridge.thinGateCoreStep_of
                (Bridge.thinGateCoreSmallStep_of Bridge.thinGateCenterStep Bridge.thinGateIrrStep)
                Bridge.thinGateCoreOneStep))
            (Bridge.RootOne.thinGateOneStep_of Bridge.thinGateOne_kOne))
          (Bridge.thinTwoStepE_of_thinAllBadFalse h.thinAllBadFalse))))
    (Moufang.exceptionalGlobalStepNJ2_of_noPlane (Moufang.exceptionalNoPlaneStepNJ2_of_cases
      (Moufang.exceptionalLeviStep_of_tim75 hT Bridge.caseICommPQInput_holds)
      Bridge.exceptionalNoLeviPlaneStep_holds
      (Moufang.exceptionalNoLeviTO5StepNJ2_of_diam4
        (Moufang.excDiam4InputNJ2_of Moufang.Deep.excThreeNearInput h.exceptionalCyc))))
    (fun _ _ _ hH' hNP => Bridge.commConnected_of_noPolar
      (Bridge.asc73Input_of_theoremTwo CFSG.ShultStronglyClosedTI.theoremTwo) hH' hNP)
    arsInput hH hl
  exact ⟨hc, hs, hm⟩

theorem ARS.output_of_hyp (G : Type) [Group G] (R : Set (Subgroup G)) (h : ARS.Hyp G R) :
    ARS.Output G R :=
  ARS.output_of_step (ARS.inductionStep_of_cases ARS.caseLStep
    (ARS.caseHStep_of_frameInput ARS.caseHFrameInput) ARS.caseBStep
    (ARS.caseMaxStep_of_inputs ARS.degenerate813Input
      (ARS.caseOAStep_of_inputs₄ ARS.oaNonSimplyLacedInput ARS.oaDegenerateInput)
      (ARS.caseMStep_of_frame (Transvection.subgroupTransvectionStatementFrame_of
        (Transvection.transvectionStatementFrame_of_large
          Transvection.transvectionStatementFrameLarge)))
      (ARS.caseEStep_of ARS.ExclNS.caseENonSimplyLacedInput))) G R h

@[expose] def RootOutcomeSL (G : Type) [Group G] (D : Set G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ (∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) ∧
    ((∃ n, 3 ≤ n ∧ LieModel G .PSL n 2 f) ∨ (∃ n, 4 ≤ n ∧ LieModel G .POmegaPlus n 2 f) ∨
      LieModel G .E6 0 2 f ∨ LieModel G .E7 0 2 f ∨ LieModel G .E8 0 2 f)

theorem rootOutcome {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) :
    RootOutcomeSL G D ∨
      (ARS.NonSimplyLacedOutcome G ∧ ARS.NSLData G (rootClass D)) := by
  obtain ⟨hc, hs, hm⟩ := largeClosures hH hl
  have h := arsHyp_rootClass hH hc hs hm
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have hcard : ∀ {f : ℕ}, (∀ E ∈ rootClass D, Nat.card E = 2 ^ f) →
      ∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f :=
    fun hE d hd => hE _ ⟨d, hd, rfl⟩
  rcases ARS.output_of_hyp G (rootClass D) h with ⟨m, hm2, A, B, hX, hgen⟩ |
      ⟨m, hm4, A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | hns
  · rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      obtain ⟨f, hf, hE, hL⟩ := hX.lieModel_A_two hR hiso hZ hgen
      exact Or.inl ⟨f, hf, hcard hE, Or.inl ⟨3, le_rfl, hL⟩⟩
    · obtain ⟨f, hf, hE, hL⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      exact Or.inl ⟨f, hf, hcard hE, Or.inl ⟨m + 1, by omega, hL⟩⟩
  · obtain ⟨f, hf, hE, hL⟩ := hX.lieModel_D hR hiso hZ hm4 hgen
    exact Or.inl ⟨f, hf, hcard hE, Or.inr (Or.inl ⟨m, hm4, hL⟩)⟩
  · obtain ⟨f, hf, hE, hL⟩ := hX.lieModel_E6 hR hiso hZ hgen
    exact Or.inl ⟨f, hf, hcard hE, Or.inr (Or.inr (Or.inl hL))⟩
  · obtain ⟨f, hf, hE, hL⟩ := hX.lieModel_E7 hR hiso hZ hgen
    exact Or.inl ⟨f, hf, hcard hE, Or.inr (Or.inr (Or.inr (Or.inl hL)))⟩
  · obtain ⟨f, hf, hE, hL⟩ := hX.lieModel_E8 hR hiso hZ hgen
    exact Or.inl ⟨f, hf, hcard hE, Or.inr (Or.inr (Or.inr (Or.inr hL)))⟩
  · exact Or.inr hns

end CFSG.Timmesfeld
