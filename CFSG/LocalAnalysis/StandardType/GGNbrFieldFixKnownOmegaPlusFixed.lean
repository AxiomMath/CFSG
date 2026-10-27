module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownOmegaPlusDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SignLines
public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

namespace FieldFixOmegaPlus

variable {K : Type} [Field K] {m : ℕ}

theorem inclHom_injective (k : Subfield K) {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
    {Q : QuadraticForm K (Fin d → K)} (hext : IsExtension k Q₀ Q) :
    Function.Injective (inclHom k hext) := by
  intro a b h
  have h' : ((inclHom k hext a : matrixDerived Q) : GL (Fin d) K) =
      ((inclHom k hext b : matrixDerived Q) : GL (Fin d) K) := congrArg _ h
  rw [inclHom_val, inclHom_val] at h'
  apply Subtype.ext
  apply Units.ext
  apply Matrix.map_injective (f := k.subtype) k.subtype_injective
  simpa only [glIncl_val] using congrArg (fun z : GL (Fin d) K => z.val) h'

theorem exists_inclHom_eq_of_fixed [Finite K] [CharP K 2] (k : Subfield K) {σ : K ≃+* K} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p) (hσk : ∀ x, x ∈ k ↔ σ x = x)
    (hm : 3 ≤ m) {X : matrixDerived (coordinateQuadPlus m K)}
    (hX : glFieldAut (Fin (2 * m)) K σ X.val = X.val) :
    ∃ Y : matrixDerived (coordinateQuadPlus m k),
      inclHom k (coordinateQuadPlus_isExtension k m) Y = X := by
  have hS := CFSG.RankThree.PartOne.KCOrthogonalSubfield.subfieldSetup_plus k hσk hp hp2 hσ hm
  obtain ⟨x, hx⟩ := exists_glIncl_of_fixed k hσk hX
  have hiso : x ∈ matrixIsometries (coordinateQuadPlus m k) :=
    mem_isometries_of_glIncl k hS.hext
      (hx ▸ matrixDerived_le_isometries (coordinateQuadPlus m K) X.2)
  have hxD : x ∈ matrixDerived (coordinateQuadPlus m k) :=
    CFSG.RankThree.PartOne.FieldFix.mem_matrixDerived_of_glIncl hS.hnd₀ hS.hT₀ hS.hnd hiso
      (hx ▸ X.2)
  refine ⟨⟨x, hxD⟩, Subtype.ext ?_⟩
  rw [inclHom_val]
  exact hx

end FieldFixOmegaPlus

end CFSG.StandardType

end
