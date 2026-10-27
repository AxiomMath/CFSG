module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddToral
public import CFSG.LieType.Chevalley.LangNormalizerInvolutionTorus
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitRankOne
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

namespace CFSG.StandardType.ExcSplitRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem componentRoots_eq_pair {τ : Tag}
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {α : Fin τ.rank → ℤ}
    (hker : kernelRoots χ = {α, -α}) (hαk : α ∈ kernelRoots χ) :
    componentRoots χ (⟦⟨α, hαk⟩⟧ : KernelComponent χ) = {α, -α} := by
  have hself : α ∈ componentRoots χ (⟦⟨α, hαk⟩⟧ : KernelComponent χ) := ⟨hαk, rfl⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro β ⟨hβ, -⟩
    rw [hker] at hβ
    exact hβ
  · rintro β (rfl | rfl)
    · exact hself
    · exact CFSG.ComponentClassification.ExcSelector.neg_mem_componentRoots hself

end CFSG.StandardType.ExcSplitRootGen

end
