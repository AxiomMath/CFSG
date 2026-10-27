module

public import CFSG.LocalAnalysis.StandardType.SpEightCoordinates
public import CFSG.GF2Type.SmithTypeE.E7.Omega
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Blueprint.Catalog
public import CFSG.Fischer.Classification.Defs
public import CFSG.GF2Type.Smith1980Orthogonal
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S12Cent
public import CFSG.LargeExtraspecial.S12Six
public import CFSG.LargeExtraspecial.S14C10Apply
public import CFSG.LargeExtraspecial.S14Claims
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S4EightMain
public import CFSG.LargeExtraspecial.S4SevenB3
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.Blueprint CFSG.Blueprint.EvenSource

theorem map_subtype_commutator_matrixOrthogonal :
    (commutator ↥(matrixOrthogonal Q0)).map (matrixOrthogonal Q0).subtype = StatedOmega Q0 := by
  rw [statedOmega_eq_commutator, commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

noncomputable def commutatorMatrixOrthogonalEquiv :
    ↥(commutator ↥(matrixOrthogonal Q0)) ≃* ↥(StatedOmega Q0) :=
  (Subgroup.equivMapOfInjective _ (matrixOrthogonal Q0).subtype
    (matrixOrthogonal Q0).subtype_injective).trans
    (MulEquiv.subgroupCongr map_subtype_commutator_matrixOrthogonal)

noncomputable def commutatorMatrixOrthogonalEquivProj :
    ↥(commutator ↥(matrixOrthogonal Q0)) ≃* StatedProj (StatedOmega Q0) :=
  commutatorMatrixOrthogonalEquiv.trans (CFSG.GF2Type.SmithTypeE.OmegaPlus.projEquiv 4 _)

theorem isSimpleGroup_commutator_matrixOrthogonal :
    IsSimpleGroup ↥(commutator ↥(matrixOrthogonal Q0)) := by
  haveI : IsSimpleGroup (StatedProj (StatedOmega Q0)) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (K := ZMod 2)
      (n := 4) (by norm_num)
  exact commutatorMatrixOrthogonalEquivProj.isSimpleGroup

theorem lieModel_commutator_matrixOrthogonal :
    LieModel ↥(commutator ↥(matrixOrthogonal Q0)) .POmegaPlus 4 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, le_rfl⟩, ZMod 2, inferInstance, inferInstance,
    by simp, ⟨commutatorMatrixOrthogonalEquivProj⟩⟩

end CFSG.StandardType.SpEight
