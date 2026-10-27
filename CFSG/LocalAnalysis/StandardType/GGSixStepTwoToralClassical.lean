module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralCoord

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGStepTwoCoordModelOn (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∃ (r : ℕ) (O : Subgroup (ZMod p)ˣ) (ι : Multiplicative (Fin r → ZMod p) →* G),
        StepTwoToral.GGStepTwoCoords p r O ι Bs (ggG0 p B x L D J) D
          (GGStepTwoPair p B Bs x L D J)

theorem ggStepTwoToralWitnessOn_of_coordModel {t : StatedLieTag} (h : GGStepTwoCoordModelOn t) :
    GGStepTwoToralWitnessOn t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hlin b L₁ hpair
  obtain ⟨r, O, ι, hcoord⟩ := h G p B Bs x L D J n f ψ hctx s1 hlin
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hDB : D ≤ B := hctx.2.2.1.1.1
  have hDcard : Nat.card D = p ^ 2 := hctx.2.2.1.1.2.2.1
  exact hcoord.exists_witness (hDB.trans hctx.2.1.1) hDcard hpair hpair.1 hpair.2.1

theorem ggStepTwoToralWitnessInput_of_coordModels (hPSL : GGStepTwoCoordModelOn .PSL)
    (hPSU : GGStepTwoCoordModelOn .PSU) (hPSp : GGStepTwoCoordModelOn .PSp)
    (hPlus : GGStepTwoCoordModelOn .POmegaPlus) (hMinus : GGStepTwoCoordModelOn .POmegaMinus)
    (hRest : GGStepTwoToralWitnessRestInput) : GGStepTwoToralWitnessInput :=
  ggStepTwoToralWitnessInput_of_tags (ggStepTwoToralWitnessOn_of_coordModel hPSL)
    (ggStepTwoToralWitnessOn_of_coordModel hPSU) (ggStepTwoToralWitnessOn_of_coordModel hPSp)
    (ggStepTwoToralWitnessOn_of_coordModel hPlus) (ggStepTwoToralWitnessOn_of_coordModel hMinus)
    hRest

theorem ggStepTwoCentralizerInput_of_coordModels (hPSL : GGStepTwoCoordModelOn .PSL)
    (hPSU : GGStepTwoCoordModelOn .PSU) (hPSp : GGStepTwoCoordModelOn .PSp)
    (hPlus : GGStepTwoCoordModelOn .POmegaPlus) (hMinus : GGStepTwoCoordModelOn .POmegaMinus)
    (hRest : GGStepTwoToralWitnessRestInput) : GGStepTwoCentralizerInput :=
  ggStepTwoCentralizerInput_of_fusedWitness (ggStepTwoFusedWitnessInput_of_toral
    (ggStepTwoToralWitnessInput_of_coordModels hPSL hPSU hPSp hPlus hMinus hRest))

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggSixStepTwoV2Input_of_coordModels (hSch : SchreierFor InCatalog)
    (h613 : GGStepTwoLemmaSixThirteenInput) (hA : GGStepTwoLinearFusionInput)
    (hKF : GGKGroupFusionLayerInput) (hRat : GGSixAutKHypRestAtInput)
    (h5 : GGStepTwoAutKFiveInput) (h3 : GGStepTwoAutKThreeInput)
    (hPSL : GGStepTwoCoordModelOn .PSL) (hPSU : GGStepTwoCoordModelOn .PSU)
    (hPSp : GGStepTwoCoordModelOn .PSp) (hPlus : GGStepTwoCoordModelOn .POmegaPlus)
    (hMinus : GGStepTwoCoordModelOn .POmegaMinus) (hRest : GGStepTwoToralWitnessRestInput) :
    GGSixStepTwoV2Input :=
  ggSixStepTwoV2Input_of_fused hSch h613 hA hKF hRat h5 h3 (ggStepTwoFusedWitnessInput_of_toral
    (ggStepTwoToralWitnessInput_of_coordModels hPSL hPSU hPSp hPlus hMinus hRest))

end Inputs

end CFSG.StandardType
