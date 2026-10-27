module

public import CFSG.Timmesfeld.Bridge.RootStructODBridge
public import CFSG.Timmesfeld.Bridge.RootClosureL2
public import CFSG.Timmesfeld.Bridge.SL2FactsCoord
public import CFSG.Timmesfeld.Bridge.SL2FactsTorus
public import CFSG.Timmesfeld.Bridge.SL2FactsComplement
public import CFSG.Timmesfeld.Bridge.OddLocalMain
public import CFSG.Timmesfeld.Bridge.RootStructR2CoreOne
public import CFSG.Timmesfeld.Bridge.RootStructR2OneStep
public import CFSG.Timmesfeld.Bridge.RootStructR2KOne
public import CFSG.Timmesfeld.Exceptional.DeepThreeNear
public import CFSG.Timmesfeld.Bridge.RootStructR2ManyCenter
public import CFSG.Timmesfeld.Bridge.RootStructR2Irr
public import CFSG.Timmesfeld.Bridge.RootStructN0CycleFinal
public import CFSG.Timmesfeld.Bridge.RootStructN0Odd
public import CFSG.Timmesfeld.Exceptional.DeepCyc
public import CFSG.Timmesfeld.Exceptional.DeepWorldC
public import CFSG.Timmesfeld.ARSInputThm

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Open

structure OpenInputs : Prop where
  thinAllBadFalse : Bridge.ThinAllBadFalse
  exceptionalCyc : Moufang.ExcCycInput

theorem outcome_of_openInputs (h : OpenInputs) {G : Type} [Group G] {D : Set G}
    (hH : Hyp G D) : Outcome G :=
  have hT : Moufang.Tim75Thm31 := Bridge.tim75Thm31
  have hK : Bridge.ThirdKindStep :=
    Bridge.RootClosure.thirdKindStep_of_rootThreeL2 Bridge.commonNeighbour hT
      (Bridge.RootClosure.rootThreeL2Stmt_of Bridge.RootClosure.psl2SylowCoordStmt
        Bridge.RootClosure.l2TorusIrredStmt Bridge.RootClosure.naturalComplementStmt)
  Bridge.outcome_of_stepsSE_NJ2 (Bridge.largeStepSE_of_third hK Bridge.gammaResidualStep
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
    arsInput hH

theorem conclusions_of_openInputs (h : OpenInputs) (G : Type) [Group G] [Finite G] (D : Set G)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hgen : Subgroup.closure D = ⊤)
    (hodd : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (hprod : ∀ d ∈ D, ∀ e ∈ D,
      orderOf (d * e) = 2 ∨ orderOf (d * e) = 4 ∨ Odd (orderOf (d * e)))
    (hfour : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D)
    (hnondeg : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) :
    (IsSimpleGroup G ∧
      ((Nat.card G ∈ lieOrdersChar 2 ∧
          (∀ n f : ℕ, 2 ≤ n → 1 ≤ f → Nat.card G ≠ ordTwistedA n (2 ^ f)) ∧
          (∀ f : ℕ, 1 ≤ f → Nat.card G ≠ ordBC 2 (2 ^ f))) ∨
        Nonempty (G ≃* PSU3 3 1) ∨
        Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
        Nat.card G = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7)) ∧
    ((EvenLieType G ∧
      (∀ n f : ℕ, 3 ≤ n → 1 ≤ f → ¬ LieModel G .PSU n 2 f) ∧
      (∀ f : ℕ, 1 ≤ f → ¬ LieModel G .PSp 2 2 f)) ∨
    LieModel G .PSU 3 3 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
      NativeSporadic.IsSporadic G .J2) := by
  have hH : Hyp G D := ⟨inferInstance, hclass, ⟨hinv, hprod, hfour⟩, hgen, hodd, hO2, hnondeg⟩
  have ho := outcome_of_openInputs h hH
  exact ⟨decl1_of_outcome ho, decl2_of_outcome ho⟩

theorem openInputs_holds : OpenInputs where
  thinAllBadFalse := Bridge.thinAllBadFalse_of_cycleOddStep
    fun _ _ _ h hc hs hconn hAll h3 hbad hF hU _ hg _ hP =>
      Bridge.TorusPath.false_of_odd h hc hs hconn hAll h3 hbad hF hU hg hP
  exceptionalCyc := Moufang.excCycInput_of Moufang.excWorldCInput

theorem outcome {G : Type} [Group G] {D : Set G} (hH : Hyp G D) : Outcome G :=
  outcome_of_openInputs openInputs_holds hH

theorem conclusions (G : Type) [Group G] [Finite G] (D : Set G)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hgen : Subgroup.closure D = ⊤)
    (hodd : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (hprod : ∀ d ∈ D, ∀ e ∈ D,
      orderOf (d * e) = 2 ∨ orderOf (d * e) = 4 ∨ Odd (orderOf (d * e)))
    (hfour : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D)
    (hnondeg : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) :
    (IsSimpleGroup G ∧
      ((Nat.card G ∈ lieOrdersChar 2 ∧
          (∀ n f : ℕ, 2 ≤ n → 1 ≤ f → Nat.card G ≠ ordTwistedA n (2 ^ f)) ∧
          (∀ f : ℕ, 1 ≤ f → Nat.card G ≠ ordBC 2 (2 ^ f))) ∨
        Nonempty (G ≃* PSU3 3 1) ∨
        Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
        Nat.card G = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7)) ∧
    ((EvenLieType G ∧
      (∀ n f : ℕ, 3 ≤ n → 1 ≤ f → ¬ LieModel G .PSU n 2 f) ∧
      (∀ f : ℕ, 1 ≤ f → ¬ LieModel G .PSp 2 2 f)) ∨
    LieModel G .PSU 3 3 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
      NativeSporadic.IsSporadic G .J2) :=
  conclusions_of_openInputs openInputs_holds G D hclass hinv hgen hodd hO2 hprod hfour hnondeg

end CFSG.Timmesfeld
