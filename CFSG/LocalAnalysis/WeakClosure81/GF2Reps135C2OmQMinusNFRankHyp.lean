module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFAct
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bInvol
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso
import CFSG.Assembly.QuasithinDefs
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.BorelTits.CompleteFlag
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
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.StandardType

@[expose] def omqnfHyp (n : ℕ) (K : Type*) [Field K] : Submodule K (Vm n K) :=
  Submodule.span K (Set.range (omqnfFrame n K))

@[expose] def omqnfPlane (n : ℕ) (K : Type*) [Field K] : Submodule K (Vm n K) :=
  Submodule.span K (Set.range (planeVec n (K := K)))

theorem omqnf_linearIndependent_frame (n : ℕ) (K : Type*) [Field K] :
    LinearIndependent K (omqnfFrame n K) := by
  have h := (Pi.basisFun K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).linearIndependent.comp
    (Sum.elim (fun a => Sum.inl a) (fun a => Sum.inr (Sum.inl a)))
    (by
      intro x y hxy
      rcases x with a | a <;> rcases y with b | b <;> simp_all)
  convert h using 1
  funext x
  rcases x with a | a <;> simp [omqnfFrame, eVec, fVec]

open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7b in
theorem omqnf_finrank_span_perm_sub {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → V}
    (he : LinearIndependent K e) (σ : Equiv.Perm ι) (hσ : σ * σ = 1) :
    Module.finrank K (Submodule.span K (Set.range fun x => e (σ x) - e x)) =
      σ.support.card / 2 := by
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun p : Equiv.Perm ι => p x) hσ
    simpa [Equiv.Perm.mul_apply] using this
  have hsymm : σ.symm = σ := by
    ext x
    rw [Equiv.symm_apply_eq, hσσ]
  let E : (ι → K) →ₗ[K] V := Fintype.linearCombination K e
  have hE : Function.Injective E := he.fintypeLinearCombination_injective
  let M : Matrix ι ι K := permMat K σ - 1
  have hrank : M.rank * 2 + Fintype.card {x // σ x = x} = Fintype.card ι :=
    rank_permMat_sub_one σ hσ
  let P : (ι → K) →ₗ[K] (ι → K) := LinearMap.funLeft K K σ
  have hP : (permMat K σ).mulVecLin = P := by
    refine LinearMap.ext fun v => funext fun y => ?_
    rw [Matrix.mulVecLin_apply, permMat_mulVec_apply, hsymm]
    rfl
  have hM : M.mulVecLin = P - 1 := by
    refine LinearMap.ext fun v => ?_
    have h1 : P v = (permMat K σ).mulVec v := by rw [← hP]; rfl
    rw [Matrix.mulVecLin_apply, LinearMap.sub_apply, h1]
    simp only [M, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  have hspan : Submodule.span K (Set.range fun x => e (σ x) - e x) =
      Submodule.map E (LinearMap.range (P - 1)) := by
    rw [LinearMap.range_eq_map, ← (Pi.basisFun K ι).span_eq, Submodule.map_span,
      Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
    congr 1
    refine congrArg Set.range (funext fun x => ?_)
    simp only [Function.comp_apply, Pi.basisFun_apply, LinearMap.sub_apply, map_sub]
    have hPs : P (Pi.single x 1) = Pi.single (σ x) 1 := by
      funext y
      simp only [P, LinearMap.funLeft_apply, Pi.single_apply]
      by_cases h : y = σ x
      · subst h
        simp [hσσ]
      · have h' : ¬ σ y = x := fun h' => h (by rw [← h', hσσ])
        simp [h, h']
    rw [hPs]
    simp [E, Fintype.linearCombination_apply_single]
  rw [hspan, ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective E hE _)]
  have h2 : Module.finrank K (LinearMap.range (P - 1)) = M.rank := by
    rw [Matrix.rank, hM]
  rw [h2]
  have h3 : σ.support.card + Fintype.card {x // σ x = x} = Fintype.card ι := by
    classical
    rw [Fintype.card_subtype, add_comm, ← Finset.card_univ]
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
      (fun x => σ x = x)
    convert this using 2
    congr 1
  omega

theorem omqnf_finrank_map_hyp {n : ℕ} {K : Type*} [Field K] {b c : K}
    {π : Equiv.Perm (Fin (n - 1))} {s : Fin (n - 1) → ℤ} {T : Vm n K ≃ₗ[K] Vm n K}
    (h : omqnfActs n b c π s T) (hσ : spMonoPerm π s * spMonoPerm π s = 1) :
    Module.finrank K
        (Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfHyp n K)) =
      (spMonoPerm π s).support.card / 2 := by
  have hmap : Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfHyp n K) =
      Submodule.span K (Set.range fun x => omqnfFrame n K (spMonoPerm π s x) -
        omqnfFrame n K x) := by
    rw [omqnfHyp, Submodule.map_span, ← Set.range_comp]
    congr 1
    refine congrArg Set.range (funext fun x => ?_)
    simp only [Function.comp_apply, LinearMap.sub_apply, LinearEquiv.coe_coe, h.1 x,
      Module.End.one_apply]
  rw [hmap]
  exact omqnf_finrank_span_perm_sub (omqnf_linearIndependent_frame n K) _ hσ

end CFSG.LocalAnalysis.WeakClosure81
