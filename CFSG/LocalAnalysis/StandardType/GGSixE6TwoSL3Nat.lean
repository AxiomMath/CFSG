module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveF4
import CFSG.Quasithin.Background.SL3SmallNat
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
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Split
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
import CFSG.Quasithin.Background.A3Structure312Iso
import CFSG.Quasithin.Background.FFC4Pair
import CFSG.Quasithin.Background.FFC4Tr2
import CFSG.Quasithin.Background.SmithB42L2L32
import CFSG.Quasithin.Background.SmithB42L2Nat
import CFSG.Quasithin.Background.SmithB42SL3Aut
import CFSG.Quasithin.Background.SmithB42SL3Base
import CFSG.Quasithin.Background.SmithB51LnRealB
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.StandardType.GGHalf Matrix

section SL3Nat

@[expose] noncomputable def scalarOmega : Matrix.SpecialLinearGroup (Fin 3) F4 :=
  ⟨Matrix.diagonal fun _ => f4Omega, by
    rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact f4Omega_pow_three⟩

theorem scalarOmega_ne_one : scalarOmega ≠ 1 := by
  intro h
  have hval := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  have h00 : f4Omega = 1 := by
    simpa [scalarOmega, Matrix.SpecialLinearGroup.coe_one] using hval
  exact f4Omega_ne_one h00

theorem scalarOmega_mem_center :
    scalarOmega ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨f4Omega, ?_, ?_⟩
  · rw [Fintype.card_fin]; exact f4Omega_pow_three
  · rw [Matrix.scalar_apply]; rfl

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem sl3_natural_form
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) F4) W) (hirr : ρ.IsIrreducible)
    (hnt : ∃ x, ρ x ≠ 1) (hdim : Module.finrank (ZMod 2) W ≤ 6) :
    ∃ (ψ : Matrix.SpecialLinearGroup (Fin 3) F4 ≃* Matrix.SpecialLinearGroup (Fin 3) F4)
      (E : W ≃+ (Fin 3 → F4)), ∀ g w,
        E (ρ g w) = ((ψ g : Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ E w :=
  by
  haveI : Fintype F4 := Fintype.ofFinite F4
  have hcard : Fintype.card F4 = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 2 (by norm_num)
  obtain ⟨ψ, hψ, E, hE⟩ :=
    CFSG.Quasithin.SL3Small.natural_of_irreducible (F := F4) (f := 2) hcard (by norm_num)
      ρ hirr hnt (by omega)
  refine ⟨MonoidHom.toMulEquiv ψ ψ ?_ ?_, E, ?_⟩
  · apply MonoidHom.ext
    intro g
    simpa [MonoidHom.comp_apply] using hψ g
  · apply MonoidHom.ext
    intro g
    simpa [MonoidHom.comp_apply] using hψ g
  · intro g w; exact hE g w

theorem sl3_scalarOmega_ne_one
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) F4) W) (hirr : ρ.IsIrreducible)
    (hnt : ∃ x, ρ x ≠ 1) (hdim : Module.finrank (ZMod 2) W ≤ 6) : ρ scalarOmega ≠ 1 := by
  intro h
  obtain ⟨ψ, E, hE⟩ := sl3_natural_form ρ hirr hnt hdim
  have hfix : ∀ x : Fin 3 → F4,
      ((ψ scalarOmega : Matrix.SpecialLinearGroup (Fin 3) F4) :
        Matrix (Fin 3) (Fin 3) F4) *ᵥ x = x := by
    intro x
    obtain ⟨w, rfl⟩ := E.surjective x
    have h1 := hE scalarOmega w
    rw [h] at h1
    simpa using h1.symm
  have hmat : ((ψ scalarOmega : Matrix.SpecialLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [hfix v, Matrix.one_mulVec]
  have hψ1 : ψ scalarOmega = 1 := by
    apply Subtype.ext
    simpa [Matrix.SpecialLinearGroup.coe_one] using hmat
  exact scalarOmega_ne_one (ψ.injective (by simp [hψ1]))

end SL3Nat

end CFSG.StandardType.GGSixE6Two
