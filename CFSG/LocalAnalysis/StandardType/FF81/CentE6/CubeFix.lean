module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatT
public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.InvolutionRank
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.HardMathSupport.GuralnickMalle.CyclicTwo
public import CFSG.HardMathSupport.GuralnickMalle.ElemAbelianTwoHom
public import CFSG.HardMathSupport.GuralnickMalle.FGeneral
public import CFSG.HardMathSupport.GuralnickMalle.JordanTensorFinal
public import CFSG.HardMathSupport.GuralnickMalle.Prop24General
public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.EndNode
public import CFSG.LargeExtraspecial.S8CorBStatement
public import CFSG.LieType.SpecialLinear.ExteriorModel.Kron
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
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.GF2n.Smith81.ELane
public import CFSG.RankThree.GF2n.Smith81.LinOddBasic
public import CFSG.RankThree.GF2n.Smith81.LinRank
public import CFSG.RankThree.GF2n.Smith81.LinStmt
public import CFSG.RankThree.GF2n.Smith81.OrthStmt
public import CFSG.RankThree.GF2n.Smith81.S81A5Root
public import CFSG.RankThree.GF2n.Smith81.S81U6Iso
public import CFSG.RankThree.GF2n.Smith81.S81VDefs
public import CFSG.RankThree.GF2n.Smith81.Sec216LocalE3
public import CFSG.RankThree.GF2n.Smith81.Sec220Local
public import CFSG.RankThree.GF2n.Smith81.Sec2FStar
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Timmesfeld.RankOne
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups Matrix
open CFSG.RankThree.GF2n.Smith81

private theorem cubeAct_stdTransvection_cubeBasis_of_not
    (I : Set.powersetCard (Fin 6) 3)
    (hI : ¬ ((5 : Fin 6) ∈ I.val ∧ (0 : Fin 6) ∉ I.val)) :
    cubeAct CFSG.Holt.SL6.stdTransvection (A5Cube.cubeBasis (ZMod 2) I) =
      A5Cube.cubeBasis (ZMod 2) I := by
  classical
  set a : GL (Fin 6) (ZMod 2) :=
    Matrix.SpecialLinearGroup.toGL CFSG.Holt.SL6.stdTransvection with ha
  set u : Fin 3 → Fin 6 → ZMod 2 := fun r => A5Cube.e (ZMod 2) (A5Cube.enum I r) with hu
  have hcB : A5Cube.cubeBasis (ZMod 2) I =
      (exteriorPower.ιMulti (ZMod 2) 3 u : A5Cube.Cube (ZMod 2)) := by
    rw [A5Cube.cubeBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family, hu]
    congr 1
    funext r
    rw [Function.comp_apply, A5Cube.enum, A5Cube.e, Pi.basisFun_apply]
  have hmul : ∀ m : Fin 6,
      (a : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ A5Cube.e (ZMod 2) m =
        A5Cube.e (ZMod 2) m + (if m = (5 : Fin 6) then A5Cube.e (ZMod 2) 0 else 0) := by
    intro m
    have hco : (a : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        1 + Matrix.single (0 : Fin 6) 5 1 := by
      rw [ha]
      exact CFSG.Holt.SL6.coe_stdTransvection
    rw [hco, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
    by_cases h5 : m = (5 : Fin 6)
    · subst h5
      simp [A5Cube.e]
    · have h5' : (5 : Fin 6) ≠ m := fun h => h5 h.symm
      simp [A5Cube.e, h5, h5']
  have himg : (exteriorPower.ιMulti (ZMod 2) 3
        (fun r : Fin 3 => (a : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ u r) :
          A5Cube.Cube (ZMod 2)) =
      (exteriorPower.ιMulti (ZMod 2) 3 u : A5Cube.Cube (ZMod 2)) := by
    by_cases h5 : (5 : Fin 6) ∈ I.val
    · have h0 : (0 : Fin 6) ∈ I.val := by
        by_contra h
        exact hI ⟨h5, h⟩
      obtain ⟨t₀, ht₀⟩ := CFSG.LieType.Chevalley.ExteriorCube.exists_enum_eq h0
      obtain ⟨t₁, ht₁⟩ := CFSG.LieType.Chevalley.ExteriorCube.exists_enum_eq h5
      have htne : t₁ ≠ t₀ := by
        intro h
        have h50 : (5 : Fin 6) = (0 : Fin 6) := by rw [← ht₁, h, ht₀]
        exact (by decide : (5 : Fin 6) ≠ 0) h50
      have hfam : (fun r => (a : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ u r) =
          Function.update u t₁ (u t₁ + u t₀) := by
        funext r
        by_cases hr : r = t₁
        · subst hr
          rw [Function.update_self, hmul, hu, ht₁]
          simp [ht₁, ht₀]
        · rw [Function.update_of_ne hr, hmul]
          have hne : A5Cube.enum I r ≠ (5 : Fin 6) := by
            intro h
            apply hr
            exact (A5Cube.enum I).injective (by rw [h, ht₁])
          simp [hu, hne]
      rw [hfam, AlternatingMap.map_update_add, Function.update_eq_self]
      have hzero : (exteriorPower.ιMulti (ZMod 2) 3 (Function.update u t₁ (u t₀)) :
          A5Cube.Cube (ZMod 2)) = 0 := by
        refine AlternatingMap.map_eq_zero_of_eq _ _ (i := t₀) (j := t₁) ?_ (Ne.symm htne)
        rw [Function.update_of_ne (Ne.symm htne), Function.update_self]
      rw [hzero, add_zero]
    · have hfam : (fun r => (a : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ u r) = u := by
        funext r
        rw [hmul, hu]
        have hne : A5Cube.enum I r ≠ (5 : Fin 6) := by
          intro h
          exact h5 (h ▸ CFSG.LieType.Chevalley.ExteriorCube.enum_mem I r)
        simp [hne]
      rw [hfam]
  calc cubeAct CFSG.Holt.SL6.stdTransvection (A5Cube.cubeBasis (ZMod 2) I)
      = A5Cube.rho (ZMod 2) a (A5Cube.cubeBasis (ZMod 2) I) := by rw [cubeAct, ha.symm]
    _ = A5Cube.rho (ZMod 2) a (exteriorPower.ιMulti (ZMod 2) 3 u) := by rw [hcB]
    _ = (exteriorPower.ιMulti (ZMod 2) 3
          (fun r : Fin 3 => (a : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ u r) :
            A5Cube.Cube (ZMod 2)) :=
        A5Cube.rho_ιMulti (ZMod 2) a u
    _ = (exteriorPower.ιMulti (ZMod 2) 3 u : A5Cube.Cube (ZMod 2)) := himg
    _ = A5Cube.cubeBasis (ZMod 2) I := hcB.symm

private def fixedTriple : Fin 14 → Set.powersetCard (Fin 6) 3 :=
  ![ ⟨{(0 : Fin 6), 1, 5}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(0 : Fin 6), 2, 5}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(0 : Fin 6), 3, 5}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(0 : Fin 6), 4, 5}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(0 : Fin 6), 1, 2}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(0 : Fin 6), 1, 3}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(0 : Fin 6), 1, 4}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(0 : Fin 6), 2, 3}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(0 : Fin 6), 2, 4}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(0 : Fin 6), 3, 4}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(1 : Fin 6), 2, 3}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(1 : Fin 6), 2, 4}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(1 : Fin 6), 3, 4}, by rw [Set.powersetCard.mem_iff]; decide⟩,
     ⟨{(2 : Fin 6), 3, 4}, by rw [Set.powersetCard.mem_iff]; decide⟩ ]

private theorem fixedTriple_injective : Function.Injective fixedTriple := by
  decide +kernel +revert

private theorem fixedTriple_fixed (i : Fin 14) :
    ¬ ((5 : Fin 6) ∈ (fixedTriple i).val ∧ (0 : Fin 6) ∉ (fixedTriple i).val) := by
  decide +kernel +revert

theorem le_fixedDim_cubeAct_stdTransvection :
    14 ≤ fixedDim (cubeAct CFSG.Holt.SL6.stdTransvection) := by
  classical
  let b := A5Cube.cubeBasis (ZMod 2)
  let f : A5Cube.Cube (ZMod 2) →ₗ[ZMod 2] A5Cube.Cube (ZMod 2) :=
    cubeAct CFSG.Holt.SL6.stdTransvection - 1
  have hspan : Submodule.span (ZMod 2) (Set.range (fun i => b (fixedTriple i))) ≤ f.ker := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hfix := cubeAct_stdTransvection_cubeBasis_of_not (fixedTriple i) (fixedTriple_fixed i)
    show (cubeAct CFSG.Holt.SL6.stdTransvection - 1)
        (A5Cube.cubeBasis (ZMod 2) (fixedTriple i)) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact hfix
  have hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun i => b (fixedTriple i)))) = 14 :=
    finrank_span_eq_card (b := fun i => b (fixedTriple i))
      (b.linearIndependent.comp fixedTriple fixedTriple_injective)
  rw [fixedDim]
  show 14 ≤ Module.finrank (ZMod 2) f.ker
  calc 14 = Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) (Set.range (fun i => b (fixedTriple i)))) := hdim.symm
    _ ≤ Module.finrank (ZMod 2) f.ker := Submodule.finrank_mono hspan

theorem isTransvec_of_le_fixedDim_cubeAct {g : SL(6, ZMod 2)} (h2 : g * g = 1) (h1 : g ≠ 1)
    (hd : 14 ≤ fixedDim (cubeAct g)) : IsTransvec g := by
  let a : GL (Fin 6) (ZMod 2) := Matrix.SpecialLinearGroup.toGL g
  have ha : a * a = 1 := by
    change Matrix.SpecialLinearGroup.toGL g * Matrix.SpecialLinearGroup.toGL g = 1
    rw [← map_mul, h2, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    exact h1 (Matrix.SpecialLinearGroup.toGL_injective (by simpa using h))
  have hrep : cubeAct g = (CFSG.HardMathSupport.GuralnickMalle.glExterior3Rep (ZMod 2)) a := by
    apply LinearMap.ext
    intro x
    rw [cubeAct, A5Cube.rho_apply_eq_map, CFSG.HardMathSupport.GuralnickMalle.glExterior3Rep_apply,
      CFSG.HardMathSupport.GuralnickMalle.glNaturalRep_eq_toLin]
  have hfix : fixedDim (cubeAct g) = Module.finrank (ZMod 2)
      (CFSG.HardMathSupport.GuralnickMalle.fixSubGen
        (CFSG.HardMathSupport.GuralnickMalle.glExterior3Rep (ZMod 2))
        (Subgroup.closure {a})) := by
    rw [fixedDim, CFSG.HardMathSupport.GuralnickMalle.fixSubGen_closure_singleton, ← hrep]
  have hbound :=
    CFSG.HardMathSupport.GuralnickMalle.finrank_fixSubGen_closure_add_two_mul_natRank_le
      (ZMod 2) a ha ha1
  rw [hfix] at hd
  have hle : CFSG.HardMathSupport.GuralnickMalle.natRank a ≤ 1 := by omega
  have hge : 1 ≤ CFSG.HardMathSupport.GuralnickMalle.natRank a :=
    CFSG.HardMathSupport.GuralnickMalle.one_le_natRank ha1
  have hnat1 : CFSG.HardMathSupport.GuralnickMalle.natRank a = 1 := le_antisymm hle hge
  rw [IsTransvec]
  change Matrix.rank ((a : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1) = 1
  rw [← CFSG.HardMathSupport.GuralnickMalle.natRank_eq_rank, hnat1]

end CFSG.StandardType.FF81.CentE6
