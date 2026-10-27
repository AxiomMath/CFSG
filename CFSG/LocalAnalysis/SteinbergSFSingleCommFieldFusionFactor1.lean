module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionBridge

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff8_factor1 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) (hK : SixKConclusion φ t i) (f7 : FF7Concl φ t i) :
    FF8FactorConcl n φ t i 0 := by
  intro v₀ hv2 hvC hvF hn h1 h0 _
  have hcard := ffTorus_card_K hS hn
  obtain ⟨μ, f, g, hμJ, hμ, hχ, hfrob⟩ := ffTorus_exists_adapted_u φ (n := n)
    (by have := hS.fc.setup.two_le; omega) hS.fc.setup.card_K i
  obtain ⟨c, hc⟩ := ffLayer_U φ i hμ hχ
  haveI := (f7.2.2.1 0).choose_spec
  exact ffBridge_scalar_section_one hcard μ hv2 (hfrob hv2 hvF) h1 h0 (f7.2.1 0)
    (fun l => ffLayer_U_normalizer φ i hμ l) (fun l => ffTorus_mem_normalizer_bot _) hc

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
