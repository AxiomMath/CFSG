module

public import CFSG.RankThree.PartOne.KE.SuzukiLangSp4Words
public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroup
public import CFSG.LieType.AlgebraicGroups.ToralCentralizerComponent
public import CFSG.LieType.AlgebraicGroups.ReducedGroupSmooth
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix WithConv CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

open scoped CFSG.ConvolutionPoints

theorem isPointConstructible_of_isPointClosed {k : Type} [Field k] {A : Type} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] {S : Set (A →ₐ[k] k)} (h : IsPointClosed k S) :
    IsPointConstructible k S := by
  obtain ⟨Z, hZ, rfl⟩ := h
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine ⟨Z, ?_, rfl⟩
  rw [← Topology.isConstructible_compl]
  exact (TopologicalSpace.NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl

section Closed

variable (k : Type) [Field k]

theorem exteriorSquareJ_map {R S : Type} [CommRing R] [CommRing S] {F : Type*} [FunLike F R S]
    [RingHomClass F R S] (f : F) :
    (CFSG.LinearAlgebra.exteriorSquareJ R).map f = CFSG.LinearAlgebra.exteriorSquareJ S := by
  ext i j
  simp only [Matrix.map_apply, CFSG.LinearAlgebra.exteriorSquareJ_apply]
  split_ifs <;> simp

@[expose] def symplecticRel : Matrix (Fin 4) (Fin 4) (GLCoord k (Fin 4)) :=
  (glEntryMatrix k (Fin 4))ᵀ * CFSG.LinearAlgebra.exteriorSquareJ (GLCoord k (Fin 4)) *
      glEntryMatrix k (Fin 4) - CFSG.LinearAlgebra.exteriorSquareJ (GLCoord k (Fin 4))

@[expose] def symplecticIdeal : Ideal (GLCoord k (Fin 4)) :=
  Ideal.span (Set.range fun p : Fin 4 × Fin 4 => symplecticRel k p.1 p.2)

theorem mem_pointsZero_symplecticIdeal (y : GLCoord k (Fin 4) →ₐ[k] k) :
    y ∈ pointsZero k (symplecticIdeal k) ↔ glPointEquiv.symm (toConv y) ∈ antiSp k := by
  set g : GL (Fin 4) k := glPointEquiv.symm (toConv y) with hg
  have hM : (glEntryMatrix k (Fin 4)).map (y : GLCoord k (Fin 4) →+* k) = glMat g := by
    ext i j
    rfl
  have key : (symplecticRel k).map (y : GLCoord k (Fin 4) →+* k) =
      (glMat g)ᵀ * minorJ k * glMat g - minorJ k := by
    have h1 : (y : GLCoord k (Fin 4) →+* k).mapMatrix (symplecticRel k) =
        (symplecticRel k).map (y : GLCoord k (Fin 4) →+* k) := rfl
    rw [← h1, symplecticRel, map_sub, map_mul, map_mul]
    simp only [RingHom.mapMatrix_apply, Matrix.transpose_map, hM, exteriorSquareJ_map, minorJ]
  rw [mem_antiSp, ← sub_eq_zero, ← key]
  constructor
  · intro h
    ext i j
    exact h _ (Ideal.subset_span ⟨(i, j), rfl⟩)
  · intro h a ha
    have hle : symplecticIdeal k ≤ RingHom.ker y := by
      rw [symplecticIdeal, Ideal.span_le]
      rintro _ ⟨p, rfl⟩
      exact congrFun (congrFun h p.1) p.2
    exact hle ha

theorem glPoints_antiSp_eq :
    glPoints ((antiSp k : Subgroup (GL (Fin 4) k)) : Set (GL (Fin 4) k)) =
      pointsZero k (symplecticIdeal k) := by
  ext y
  rw [mem_pointsZero_symplecticIdeal]
  constructor
  · rintro ⟨g, hg, rfl⟩
    simpa using hg
  · intro h
    exact ⟨_, h, by simp⟩

theorem isPointClosed_glPoints_antiSp :
    IsPointClosed k (glPoints ((antiSp k : Subgroup (GL (Fin 4) k)) : Set (GL (Fin 4) k))) := by
  rw [glPoints_antiSp_eq]
  exact isPointClosed_pointsZero _

end Closed

section Irreducible

variable (k : Type) [Field k] [IsAlgClosed k] [CharP k 2]

theorem isPointIrreducible_glPoints_antiSp :
    IsPointIrreducible k
      (glPoints ((antiSp k : Subgroup (GL (Fin 4) k)) : Set (GL (Fin 4) k))) := by
  classical
  let S : ℕ → Set (GLCoord k (Fin 4) →ₐ[k] k) := fun n =>
    Set.range fun z : TransvPoly k n →ₐ[k] k => z.comp (transvCo k n)
  have hS : ∀ n, S n = {y | ∃ c : Fin n → (Fin 4 → k) × k,
      glPointEquiv.symm (toConv y) = wordGL (List.ofFn c)} := by
    intro n
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨pointWord z, glPointEquiv_symm_comp_transvCo z⟩
    · rintro ⟨c, hc⟩
      obtain ⟨z, rfl⟩ := exists_pointWord_eq c
      refine ⟨z, ?_⟩
      apply toConv_injective
      apply glPointEquiv.symm.injective
      rw [glPointEquiv_symm_comp_transvCo]
      exact hc.symm
  have hunion : glPoints ((antiSp k : Subgroup (GL (Fin 4) k)) : Set (GL (Fin 4) k)) =
      ⋃ n, S n := by
    ext y
    simp only [Set.mem_iUnion, hS, Set.mem_ofPred_eq]
    rw [glPoints_antiSp_eq, mem_pointsZero_symplecticIdeal]
    constructor
    · intro hy
      obtain ⟨w, hw⟩ := exists_wordGL_eq hy
      refine ⟨w.length, fun i => w.get i, ?_⟩
      rw [← hw, List.ofFn_get]
    · rintro ⟨n, c, hc⟩
      rw [hc]
      exact wordGL_mem _
  rw [hunion]
  refine isPointIrreducible_iUnion_of_directed S
    (fun n => isPointIrreducible_range_of_isDomain _) fun i j => ⟨i + j, ?_, ?_⟩
  · rw [hS, hS]
    rintro y ⟨c, hc⟩
    refine ⟨Fin.append c (fun _ : Fin j => ((0 : Fin 4 → k), (0 : k))), ?_⟩
    rw [hc, List.ofFn_fin_append, wordGL_append,
      wordGL_ofFn_eq_one (fun _ : Fin j => ((0 : Fin 4 → k), (0 : k))) (fun _ => rfl), mul_one]
  · rw [hS, hS]
    rintro y ⟨c, hc⟩
    refine ⟨Fin.append (fun _ : Fin i => ((0 : Fin 4 → k), (0 : k))) c, ?_⟩
    rw [hc, List.ofFn_fin_append, wordGL_append,
      wordGL_ofFn_eq_one (fun _ : Fin i => ((0 : Fin 4 → k), (0 : k))) (fun _ => rfl), one_mul]

end Irreducible

theorem antiSp_algebraic_group_connected_smooth (k : Type) [Field k] [IsAlgClosed k]
    [CharP k 2] :
    IsPointClosed k (glPoints ((antiSp k : Subgroup (GL (Fin 4) k)) : Set (GL (Fin 4) k))) ∧
      IsConnectedAlgebraicSubgroup k (glPointSubgroup (antiSp k)) ∧
      Algebra.Smooth k (GLCoord k (Fin 4) ⧸ subgroupIdeal (glPointSubgroup (antiSp k))) ∧
      IrreducibleSpace
        (PrimeSpectrum (GLCoord k (Fin 4) ⧸ subgroupIdeal (glPointSubgroup (antiSp k)))) ∧
      ∃ e : WithConv ((GLCoord k (Fin 4) ⧸ subgroupIdeal (glPointSubgroup (antiSp k))) →ₐ[k] k) ≃*
          antiSp k, ∀ φ,
        ((e φ : antiSp k) : GL (Fin 4) k) =
          glPointEquiv.symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))) := by
  obtain ⟨hcl, hG, he⟩ := (exceptional_Lang_constructible_subgroup_closed k).2.1 (Fin 4)
    (antiSp k) (isPointConstructible_of_isPointClosed (isPointClosed_glPoints_antiSp k))
    (isPointIrreducible_glPoints_antiSp k)
  have := hG.isReduced
  have := hG.finiteType
  have := hG.isDomain
  exact ⟨hcl, hG, (smooth_of_hopfAlgebra_of_isReduced k _).1, inferInstance, he⟩

end CFSG.RankThree.PartOne.KE
