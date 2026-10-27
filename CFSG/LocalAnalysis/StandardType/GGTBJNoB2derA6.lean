module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpRank
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l48aS_scalars_eq_bot {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) :
    LargeEvenScalars (Fin 2 ⊕ Fin 2) K = ⊥ := by
  classical
  rw [largeEvenScalars_def, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨u, rfl⟩ := hx
  haveI : Subsingleton Kˣ := by
    rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_units, hK]
  rw [Subsingleton.elim u 1, map_one]

private lemma l48aS_unpack {R : Type} [Group R]
    (h : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) R) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (R ≃* LargeEvenProj
        (⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ : Subgroup (GL (Fin 2 ⊕ Fin 2) K))) := by
  simp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeSymplectic] at h
  obtain ⟨K, hK, hKf, hKcard, hcont2⟩ := h
  letI : Field K := hK
  letI : Finite K := hKf
  exact ⟨K, hK, hKf, hKcard, by simpa using hcont2⟩

theorem ggB2der_label_iso_A6 {R : Type} [Group R]
    (h : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) R) :
    Nonempty (R ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨K, hK, hKfin, hKcard, ⟨e⟩⟩ := l48aS_unpack h
  letI : Field K := hK
  letI : Finite K := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card, hKcard]
  let H : Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
    ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆
  have hbot : (LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H = ⊥ := by
    rw [l48aS_scalars_eq_bot hKf]
    simp
  have eproj : LargeEvenProj H ≃* ↥H :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have ecomm : Nonempty (↥H ≃* alternatingGroup (Fin 6)) :=
    CFSG.RankThree.CASymplecticSubfield.nonempty_commutator_mulEquiv_alternating
      (H := LargeEvenSpGroup K 2)
      (CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm hKf).some
  exact ⟨e.trans (eproj.trans ecomm.some)⟩

end CFSG.StandardType

end
