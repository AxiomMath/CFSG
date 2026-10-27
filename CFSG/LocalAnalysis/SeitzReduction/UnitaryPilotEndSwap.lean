module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapGlobal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotWeakCTSeitz
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Unique

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

@[expose] def UnitarySwapRowUnique (e : L ≃* unitaryPSU h n) (t : G) : Prop :=
  ∀ g : G, g⁻¹ * t * g ∈ normalizer (swapNeighbourJoin e : Set G) →
    g ∈ normalizer (swapNeighbourJoin e : Set G)

end Unique

section Endgame

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {f : ℕ} {K : Type}
  [Field K] {h : UnitaryFieldData 2 f K} {n : ℕ}

theorem false_of_simple_of_swapRow_unitaryRootTorus (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    (hnf : (n, f) ≠ (6, 1)) {t : G} (ht : orderOf t = 2)
    (hparam : ∀ (a b : Fin n) (hab : a ≠ b),
      Nonempty (SwapNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin n))))
    (huniq : UnitarySwapRowUnique e t) : False := by
  obtain ⟨G₁, hq, h₁₂, hsup, -, -⟩ := exists_swapFactors_iSup_neighbourCore e hn hnf hparam
  exact LinearPilot.false_of_simple_of_swapFactors ht hq h₁₂ hsup huniq

end Endgame

section SeitzSwap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem false_of_swapRow_unitaryRootTorus (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h n)
    (hn : 6 ≤ n) (hnf : (n, f) ≠ (6, 1)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hrow : ∀ (a b : Fin n) (hab : a ≠ b), UnitaryRootTorusSwapRow e t hab)
    (huniq : UnitarySwapRowUnique e t) : False := by
  have := hset.1
  refine false_of_simple_of_swapRow_unitaryRootTorus e hn hnf ht (fun a b hab => ?_) huniq
  obtain ⟨htX, hKc⟩ := hrow a b hab
  exact nonempty_swapNeighbourParam_of_swapRow h hset e hn htC ht hab htX hKc

end SeitzSwap

end CFSG.SeitzReduction.UnitaryPilot
