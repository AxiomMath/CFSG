module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank

theorem ggL44CenterTrivialInput_of_certificates :
    GGL44CenterTrivialInput := by
  intro Y _ _ hY hmod
  exact CFSG.ComponentClassification.CatFC.center_eq_bot_of_quasisimple_psl44 hY
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hmod⟩)

end CFSG.StandardType

end
