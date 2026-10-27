module

public import CFSG.RankThree.PartOne.KE.E6A3Sigma
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.KGL.TwLayer

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Classical2
open scoped MatrixGroups


variable {L : Type} [Field L]

theorem e6rhoJ3_transvection_charTwo [CharP L 2] {i j : Fin 4} (hij : i ≠ j) (t : L) :
    e6rhoJ3 L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (chainRoot chain134 i j) t := by
  obtain ⟨e, he, h⟩ := a3RootFamily_all (K := L) i j hij
  have hee : ((e : ℤ) : L) = 1 := by
    rcases he with rfl | rfl
    · simp
    · simp [CharTwo.neg_eq]
  have hmem := pinnedX_mem_a3Group (K := L) (chainRoot134_mem_parabolicRoots hij) t
  have hrep : a3Rep L ⟨pinnedX Tag.E6 L (chainRoot chain134 i j) t, hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij t := by
    apply Subtype.ext
    rw [coe_a3Rep, h, CFSG.LinearGroups.coe_transvection, hee, one_mul]
  rw [← hrep]
  exact e6rhoJ3_a3Rep hmem

theorem rhoSigmaE6A3_transvection_charTwo [CharP L 2] (u : WeylGroup Tag.E6) {i j : Fin 4}
    (hij : i ≠ j) (t : L) :
    rhoSigmaE6A3 L u (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (sigmaRootE6A3 u i j) t := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L u
    (chainRoot134_mem_parabolicRoots hij).1
  have hε1 : ε = 1 := by
    have e2 : (2 : L) = 0 := CharTwo.two_eq_zero
    have h2 : (ε + 1) * (ε + 1) = 0 := by
      linear_combination hε + (ε + 1) * e2
    have := mul_self_eq_zero.1 h2
    linear_combination this - e2
  rw [rhoSigmaE6A3_apply, e6rhoJ3_transvection_charTwo hij, h, hε1, one_mul,
    sigmaRootE6A3_eq_smul]

theorem step_rhoSigmaE6A3 [CharP L 2] (Fr : L →+* L) (step : ModGL Tag.E6 L →* ModGL Tag.E6 L)
    (hstep : ∀ γ, IsRoot Tag.E6 γ → ∀ c, step (pinnedX Tag.E6 L γ c) = pinnedX Tag.E6 L (-γ) (Fr c))
    (u : WeylGroup Tag.E6) (X : SL(4, L)) :
    step (rhoSigmaE6A3 L u X) = rhoSigmaE6A3 L u (stdUnitary Fr X) := by
  have h : step.comp (rhoSigmaE6A3 L u) = (rhoSigmaE6A3 L u).comp (stdUnitary (ν := 4) Fr) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 4) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [rhoSigmaE6A3_transvection_charTwo, stdUnitary_transvection,
      hstep _ (isRoot_sigmaRootE6A3 u hij), rhoSigmaE6A3_transvection_charTwo, sigmaRootE6A3_neg,
      CharTwo.neg_eq (Fr t)]
  exact DFunLike.congr_fun h X

theorem inf_eqLocus_eq_map_fix [CharP L 2] (Fr : L →+* L)
    (step : ModGL Tag.E6 L →* ModGL Tag.E6 L)
    (hstep : ∀ γ, IsRoot Tag.E6 γ → ∀ c,
      step (pinnedX Tag.E6 L γ c) = pinnedX Tag.E6 L (-γ) (Fr c))
    (u : WeylGroup Tag.E6) (σ' : L ≃+* L) (hσ' : σ'.toRingHom = Fr) :
    (rhoSigmaE6A3 L u).range ⊓ step.eqLocus (MonoidHom.id _) =
      (fixSubgroup (stdUnitaryEquiv (ν := 4) σ')).map (rhoSigmaE6A3 L u) := by
  ext y
  constructor
  · rintro ⟨⟨X, rfl⟩, hyF⟩
    have hyF' : step (rhoSigmaE6A3 L u X) = rhoSigmaE6A3 L u X := hyF
    have h1 := step_rhoSigmaE6A3 Fr step hstep u X
    have h2 : stdUnitary Fr X = X :=
      rhoSigmaE6A3_injective u (h1.symm.trans hyF')
    refine ⟨X, (mem_fixSubgroup _).2 ?_, rfl⟩
    rw [stdUnitaryEquiv_apply, hσ']
    exact h2
  · rintro ⟨X, hX, rfl⟩
    refine ⟨⟨X, rfl⟩, ?_⟩
    have hX' := (mem_fixSubgroup _).1 hX
    rw [stdUnitaryEquiv_apply, hσ'] at hX'
    change step (rhoSigmaE6A3 L u X) = rhoSigmaE6A3 L u X
    rw [step_rhoSigmaE6A3 Fr step hstep u X, hX']

end CFSG.StandardType.KGL.TwLayer

end
