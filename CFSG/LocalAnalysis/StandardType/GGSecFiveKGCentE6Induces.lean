module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEReduce
import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
import CFSG.LocalAnalysis.SeitzReduction.E6PilotAmalgam
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.ClassicalInvolution.Balance.PassTwoFinal
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

namespace KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem commute_of_rootChar_eq_one_E6
    {k : Type} [Field k] [Finite k] {G : Type*} [Group G]
    {ψ : ↥(Minuscule.e6Data_valid.minGroup k) →* G} {d : G} {a : Fin Tag.E6.rank → kˣ}
    (ha : LayerSixE.GGInduces (Isogeny.e6Isogeny k) ψ d (rootDiagAutHom .E6 k a))
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) (hχ : rootChar a β = 1)
    (hd : ∃ h ∈ ggTorus (Minuscule.e6Datum k), ∀ z ∈ (Minuscule.e6Datum k).rootGroup β,
      d * ψ z * d⁻¹ = ψ (h * z * h⁻¹)) :
    ∀ z ∈ (Minuscule.e6Datum k).rootGroup β, Commute d (ψ z) := by
  intro z hz
  obtain ⟨h, hh, hdh⟩ := hd
  have hβΦ : β ∈ (Minuscule.e6Datum k).roots :=
    (Minuscule.e6Data_valid.mem_minDatum_roots Minuscule.isFiniteType_cartan_E6 k).2 hβ
  simp only [ggTorus, Subgroup.mem_iInf] at hh
  obtain ⟨χ, hχh⟩ := PsiDiag.Minu.conj_xm_eq_of_mem_normalizer Minuscule.e6Data_valid k (hh β hβΦ)
  obtain ⟨c, rfl⟩ := (Minuscule.e6Data_valid.mem_rootGroup k).1 hz
  have h1 := ha (Minuscule.e6Data_valid.xm k β c) (Minuscule.e6Data_valid.xm k β (χ * c))
    (by rw [hdh _ hz, hχh])
  rw [Isogeny.e6Isogeny_xm k hβ, Isogeny.e6Isogeny_xm k hβ, Isogeny.yPar, Isogeny.yPar] at h1
  change _ = rootDiagAut .E6 k a _ at h1
  rw [CFSG.ClassicalInvolution.Balance.rootDiagAut_xPar a hβ, hχ, Units.val_one, one_mul] at h1
  have hs : (Isogeny.relSignOr (rootOperatorFamily .E6) Adjoint.e6AdjData_valid β : k) *
      (Isogeny.relSignOr (rootOperatorFamily .E6) Adjoint.e6AdjData_valid β : k) = 1 :=
    Isogeny.relSignOr_mul_self β
  have h4 : χ * c = c :=
    mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hs) (Adjoint.xPar_injective hβ h1)
  have h5 := hdh _ hz
  rw [hχh, h4] at h5
  exact mul_inv_eq_iff_eq_mul.1 h5

theorem ggInduces_fix_rootSubgroup_E6
    {k : Type} [Field k] [Finite k] {G : Type*} [Group G]
    {ψ : ↥(Minuscule.e6Data_valid.minGroup k) →* G} {t : G} {α : MulAut (adjointGroup .E6 k)}
    (hα : LayerSixE.GGInduces (Isogeny.e6Isogeny k) ψ t α) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot .E6 β) (ht : ∀ z ∈ (Minuscule.e6Datum k).rootGroup β, Commute t (ψ z)) :
    ∀ x : adjointGroup .E6 k, (x : ModGL .E6 k) ∈ rootSubgroup .E6 k β → α x = x := by
  intro x hx
  rw [← CFSG.SeitzReduction.E6Pilot.map_subtype_rootGroup_E6 hβ] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  obtain rfl : y = x := Subtype.ext hyx
  change y ∈ Adjoint.rootGroup (rootOperatorFamily .E6) k β at hy
  rw [← CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup k hβ] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact (hα z z (by rw [(ht z hz).eq, mul_inv_cancel_right])).symm

end KGCentE6

end CFSG.StandardType

end
