module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreHom
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenFrame
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenPin
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Classical2 CFSG.GF2Type.SmithTypeE
open scoped MatrixGroups

open Matrix

private lemma langRatBD_uSL_eq_transvection {K : Type} [Field K] (t : K) :
    uSL t = Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.transvection_coe, coe_uSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single_apply]

private lemma langRatBD_vSL_eq_transvection {K : Type} [Field K] (t : K) :
    vSL t = Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.transvection_coe, coe_vSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single_apply]

private lemma langRatBD_transvection_congr {n : ℕ} {K : Type} [Field K] {i i' j j' : Fin n}
    (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i') (hj : j = j') (t : K) :
    Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij' t := by
  subst hi
  subst hj
  exact Subtype.ext rfl

private lemma langRatBD_diagUnitOne_fix_HSL {Ω : Type} [Field Ω] (s ζ : Ωˣ) :
    CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) (HSL ζ) =
      HSL ζ := by
  refine Subtype.ext ?_
  rw [CFSG.RankThree.Classical.coe_conjSL, CFSG.RankThree.Classical.coe_diagUnitOne,
    CFSG.RankThree.Classical.coe_diagUnitOne_inv, CFSG.LieType.Chevalley.coe_HSL]
  have hs : (s : Ω) * (s : Ω)⁻¹ = 1 := mul_inv_cancel₀ s.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination (ζ : Ω) * hs

theorem langRatB_frame_diag
    {τ : Tag} (hτ : SimplyLacedTag τ) {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ}
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    {x y : Fin ν} (hxy : x ≠ y) (u : Lˣ) (X : SL(ν, L))
    (hX : (X : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal
      (fun j => if j = x then (u : L) else if j = y then ((u⁻¹ : Lˣ) : L) else 1)) :
    ψ X = Hel (σ x y) u := by
  set e : Fin 2 → Fin ν := ![x, y] with he_def
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [he_def] at hab ⊢
    · exact absurd hab hxy
    · exact absurd hab.symm hxy
  obtain ⟨ε1, hε1⟩ := hψ.transv x y hxy
  obtain ⟨ε2, hε2⟩ := hψ.transv y x hxy.symm
  let φ : SL2 L →* ModGL τ L := ψ.comp (slEmbed e he)
  have hix : e 0 = x := by simp [he_def]
  have hiy : e 1 = y := by simp [he_def]
  have hu : ∀ t : L, φ (uSL t) = pinnedX τ L (σ x y) ((ε1 : L) * t) := by
    intro t
    have h1 : φ (uSL t) = ψ (slEmbed e he (uSL t)) := rfl
    rw [h1, langRatBD_uSL_eq_transvection t]
    rw [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T.slEmbed_transvection]
    rw [langRatBD_transvection_congr (he.ne (by decide : (0 : Fin 2) ≠ 1)) hxy hix hiy t]
    exact hε1 t
  have hv : ∀ t : L, φ (vSL t) = pinnedX τ L (-(σ x y)) ((ε2 : L) * t) := by
    intro t
    have h1 : φ (vSL t) = ψ (slEmbed e he (vSL t)) := rfl
    rw [h1, langRatBD_vSL_eq_transvection t]
    rw [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T.slEmbed_transvection]
    rw [langRatBD_transvection_congr (he.ne (by decide : (1 : Fin 2) ≠ 0)) hxy.symm hiy hix t]
    have h2 := hε2 t
    rw [hψ.neg x y] at h2
    exact h2
  obtain ⟨s, hs⟩ := exists_comp_conjSL_eq_rootSL2 (hψ.isRoot x y hxy) φ ε1 ε2 hu hv
  have hHSL : φ (HSL u) = rootSL2 τ L (σ x y) (HSL u) := by
    have h1 := DFunLike.congr_fun hs (HSL u)
    simp only [MonoidHom.comp_apply] at h1
    rw [langRatBD_diagUnitOne_fix_HSL] at h1
    exact h1
  have hXeq : X = slEmbed e he (HSL u) := by
    apply Subtype.ext
    rw [hX]
    change Matrix.diagonal (fun j => if j = x then (u : L)
        else if j = y then ((u⁻¹ : Lˣ) : L) else 1) =
      slEmbedMat e ((HSL u : SL2 L) : Matrix (Fin 2) (Fin 2) L)
    rw [he_def]
    ext i j
    rw [Matrix.diagonal_apply]
    unfold slEmbedMat CFSG.ClassicalInvolution.Models.SymplecticPairs.inclMat
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.transpose_apply, Matrix.of_apply, Fin.sum_univ_two, coe_HSL,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    clear hu hv hs hHSL hε1 hε2 ε1 ε2 s φ hψ hX hτ he
    by_cases hix : i = x <;> by_cases hiy : i = y <;>
      by_cases hjx : j = x <;> by_cases hjy : j = y <;>
      simp_all [eq_comm] <;> ring
  calc ψ X = ψ (slEmbed e he (HSL u)) := by rw [hXeq]
    _ = φ (HSL u) := rfl
    _ = rootSL2 τ L (σ x y) (HSL u) := hHSL
    _ = Hel (σ x y) u := (Hel_root_eq_rootSL2 hτ (hψ.isRoot x y hxy) u).symm

end CFSG.StandardType.LangRat
