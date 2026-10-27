module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionFactor1
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionFactor2
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionFactor3
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionFactor4
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionFactor5
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionFactor6

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff8b (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) (hK : SixKConclusion φ t i) (f7 : FF7Concl φ t i) :
    ∀ v₀ : G, v₀ * v₀ = 1 → v₀ ∈ centralizer ({t} : Set G) →
      (∀ l : L, ((φ.symm ((frobAut K ^ (n / 2)) (φ l)) : L) : G) = v₀ * l * v₀⁻¹) → Even n →
      (∀ k : Fin 7, v₀ ∈ normalizer (ffSeries φ t i k : Set G)) →
        ∀ k : Fin 6, Nat.card (ffSeries φ t i k.succ ⊓ centralizer ({v₀} : Set G) : Subgroup G) ^ 2 =
          Nat.card (ffSeries φ t i k.succ) := by
  intro v₀ hv2 hvC hvF hn hvN
  have hle := f7.2.1
  have hNE := f7.2.2.1
  haveI hNorm : ∀ k : Fin 6,
      ((ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ)).Normal :=
    fun k => (hNE k).choose
  haveI hEA : ∀ k : Fin 6, IsElementaryAbelian 2 (↥(ffSeries φ t i k.succ) ⧸
      (ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ)) :=
    fun k => (hNE k).choose_spec
  refine ffBridge_card_sq (a := v₀) hv2 (r := 6) (ffSeries φ t i) rfl hle hvN ?_
  intro k
  fin_cases k
  · exact sixFF_ff8_factor1 hS hH hE hK f7 v₀ hv2 hvC hvF hn (hvN _) (hvN _)
  · exact sixFF_ff8_factor2 hS hH hE hK f7 v₀ hv2 hvC hvF hn (hvN _) (hvN _)
  · exact sixFF_ff8_factor3 hS hH hE hK f7 v₀ hv2 hvC hvF hn (hvN _) (hvN _)
  · exact sixFF_ff8_factor4 hS hH hE hK f7 v₀ hv2 hvC hvF hn (hvN _) (hvN _)
  · exact sixFF_ff8_factor5 hS hH hE hK f7 v₀ hv2 hvC hvF hn (hvN _) (hvN _)
  · exact sixFF_ff8_factor6 hS hH hE hK f7 v₀ hv2 hvC hvF hn (hvN _) (hvN _)

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
