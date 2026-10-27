module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASuConj
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.CurtisTits.Symplectic
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
public import CFSG.LocalAnalysis.SignalizerFunctor
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

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.UnitaryPair

open Matrix CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.RankThree.Classical2

open CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

variable {K : Type} [Field K]

def xPlus (t : K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t

def xMinus (t : K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t

def H : Matrix.SpecialLinearGroup (Fin 3) K := xPlus 1 * xMinus 1 * xPlus 1

def P (μ : K) : Matrix.SpecialLinearGroup (Fin 3) K := xMinus 1 * xPlus (1 + μ)

section CharTwo

variable [CharP K 2]

private lemma toGL_H :
    Matrix.SpecialLinearGroup.toGL H =
      TauCeti.transvectionWeylElement (A := K) (show (0 : Fin 3) ≠ 2 by decide) := by
  simp only [H, xPlus, xMinus, map_mul, TauCeti.toGL_transvection_eq_transvectionUnit,
    TauCeti.transvectionWeylElement_def, CharTwo.neg_eq]
  try rfl

private lemma toGL_xPlus (t : K) :
    Matrix.SpecialLinearGroup.toGL (xPlus t) =
      TauCeti.transvectionUnit (show (0 : Fin 3) ≠ 2 by decide) t := by
  rw [xPlus, TauCeti.toGL_transvection_eq_transvectionUnit]

private lemma toGL_xMinus (t : K) :
    Matrix.SpecialLinearGroup.toGL (xMinus t) =
      TauCeti.transvectionUnit (show (2 : Fin 3) ≠ 0 by decide) t := by
  rw [xMinus, TauCeti.toGL_transvection_eq_transvectionUnit]

private lemma H_mul_xPlus (t : K) : H * xPlus t = xMinus t * H := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  simp only [map_mul, toGL_H, toGL_xPlus, toGL_xMinus]
  have hw :
      TauCeti.transvectionWeylElement (A := K) (show (0 : Fin 3) ≠ 2 by decide) *
          TauCeti.transvectionUnit (show (0 : Fin 3) ≠ 2 by decide) t *
            (TauCeti.transvectionWeylElement (A := K)
              (show (0 : Fin 3) ≠ 2 by decide))⁻¹ =
        TauCeti.transvectionUnit (show (2 : Fin 3) ≠ 0 by decide) t := by
    rw [TauCeti.transvectionWeylElement_inv,
      TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_self]
    simp only [CharTwo.neg_eq]
  rw [← hw]
  group

private lemma H_mul_xMinus (t : K) : H * xMinus t = xPlus t * H := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  simp only [map_mul, toGL_H, toGL_xPlus, toGL_xMinus]
  have hw :
      TauCeti.transvectionWeylElement (A := K) (show (0 : Fin 3) ≠ 2 by decide) *
          TauCeti.transvectionUnit (show (2 : Fin 3) ≠ 0 by decide) t *
            (TauCeti.transvectionWeylElement (A := K)
              (show (0 : Fin 3) ≠ 2 by decide))⁻¹ =
        TauCeti.transvectionUnit (show (0 : Fin 3) ≠ 2 by decide) t := by
    rw [TauCeti.transvectionWeylElement_inv,
      TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_symm]
    simp only [CharTwo.neg_eq]
  rw [← hw]
  group

private lemma H_conj_xPlus (t : K) : H * xPlus t * H⁻¹ = xMinus t := by
  rw [H_mul_xPlus]
  group

private lemma H_conj_xMinus (t : K) : H * xMinus t * H⁻¹ = xPlus t := by
  rw [H_mul_xMinus]
  group

private lemma xPlus_one_mul_self : xPlus (1 : K) * xPlus 1 = 1 := by
  rw [xPlus, ← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero]
  exact Matrix.SpecialLinearGroup.transvection_coeff_zero _

private lemma xMinus_add (a b : K) : xMinus (a + b) = xMinus a * xMinus b := by
  simp only [xMinus]
  exact Matrix.SpecialLinearGroup.transvection_add _ a b

private lemma P_mul_H (μ : K) : P μ * H = xPlus 1 * xMinus μ := by
  have h1 : xMinus (1 : K) * H = H * xPlus (1 : K) := (H_mul_xPlus (1 : K)).symm
  have h2 : xPlus (1 + μ) * H = H * xMinus (1 + μ) := (H_mul_xMinus (1 + μ)).symm
  have h3 : H * xPlus (1 : K) = xPlus (1 : K) * xMinus (1 : K) := by
    rw [H, mul_assoc, xPlus_one_mul_self, mul_one]
  calc P μ * H = xMinus 1 * (xPlus (1 + μ) * H) := by rw [P, mul_assoc]
    _ = xMinus 1 * (H * xMinus (1 + μ)) := by rw [h2]
    _ = (xMinus 1 * H) * xMinus (1 + μ) := by rw [← mul_assoc]
    _ = (H * xPlus 1) * xMinus (1 + μ) := by rw [h1]
    _ = (xPlus 1 * xMinus 1) * xMinus (1 + μ) := by rw [h3]
    _ = xPlus 1 * (xMinus 1 * xMinus (1 + μ)) := by rw [mul_assoc]
    _ = xPlus 1 * xMinus μ := by
      rw [← xMinus_add,
        show (1 : K) + (1 + μ) = μ by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]]

theorem unitary_opposite_pair_formula (σ : K →+* K) (μ : K) (hμ : μ + σ μ = 1) :
    ∀ t : K,
      stdUnitary σ (P μ * xPlus t * (P μ)⁻¹) =
        P μ * xPlus (σ t) * (P μ)⁻¹ ∧
      stdUnitary σ (P μ * xMinus t * (P μ)⁻¹) =
        P μ * xMinus (σ t) * (P μ)⁻¹ := by
  have hσμ : σ μ = 1 + μ := by
    have h2 : μ + (μ + σ μ) = μ + 1 := congrArg (fun x => μ + x) hμ
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h2
    simpa [add_comm] using h2
  have hσ1μ : σ (1 + μ) = μ := by
    rw [map_add, map_one, hσμ, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hΦP : stdUnitary σ (P μ) = P μ * H := by
    have h1 : stdUnitary σ (xMinus 1) = xPlus 1 := by
      rw [xMinus, xPlus, stdUnitary_transvection, map_one, CharTwo.neg_eq]
    have h2 : stdUnitary σ (xPlus (1 + μ)) = xMinus μ := by
      rw [xPlus, xMinus, stdUnitary_transvection, hσ1μ, CharTwo.neg_eq]
    calc stdUnitary σ (P μ)
        = stdUnitary σ (xMinus 1) * stdUnitary σ (xPlus (1 + μ)) := by rw [P, map_mul]
      _ = xPlus 1 * xMinus μ := by rw [h1, h2]
      _ = P μ * H := by rw [P_mul_H]
  have hΦxPlus (t : K) : stdUnitary σ (xPlus t) = xMinus (σ t) := by
    rw [xPlus, xMinus, stdUnitary_transvection, CharTwo.neg_eq]
  have hΦxMinus (t : K) : stdUnitary σ (xMinus t) = xPlus (σ t) := by
    rw [xMinus, xPlus, stdUnitary_transvection, CharTwo.neg_eq]
  intro t
  constructor
  · calc stdUnitary σ (P μ * xPlus t * (P μ)⁻¹)
        = (stdUnitary σ (P μ) * stdUnitary σ (xPlus t)) * (stdUnitary σ (P μ))⁻¹ := by
          simp only [map_mul, map_inv]
      _ = (P μ * H * xMinus (σ t)) * (P μ * H)⁻¹ := by rw [hΦP, hΦxPlus]
      _ = P μ * (H * xMinus (σ t) * H⁻¹) * (P μ)⁻¹ := by group
      _ = P μ * xPlus (σ t) * (P μ)⁻¹ := by rw [H_conj_xMinus]
  · calc stdUnitary σ (P μ * xMinus t * (P μ)⁻¹)
        = (stdUnitary σ (P μ) * stdUnitary σ (xMinus t)) * (stdUnitary σ (P μ))⁻¹ := by
          simp only [map_mul, map_inv]
      _ = (P μ * H * xPlus (σ t)) * (P μ * H)⁻¹ := by rw [hΦP, hΦxMinus]
      _ = P μ * (H * xPlus (σ t) * H⁻¹) * (P μ)⁻¹ := by group
      _ = P μ * xMinus (σ t) * (P μ)⁻¹ := by rw [H_conj_xPlus]

theorem unitary_opposite_pair_fixed_iff (σ : K →+* K) (μ : K) (hμ : μ + σ μ = 1) :
    ∀ t : K,
      (stdUnitary σ (P μ * xPlus t * (P μ)⁻¹) = P μ * xPlus t * (P μ)⁻¹ ↔ σ t = t) ∧
      (stdUnitary σ (P μ * xMinus t * (P μ)⁻¹) = P μ * xMinus t * (P μ)⁻¹ ↔ σ t = t) := by
  intro t
  have hpair := unitary_opposite_pair_formula σ μ hμ t
  have hinjPlus : Function.Injective (fun s : K => P μ * xPlus s * (P μ)⁻¹) := by
    intro s s' h
    refine Matrix.SpecialLinearGroup.transvection_injective (show (0 : Fin 3) ≠ 2 by decide) ?_
    have := congrArg (fun z => (P μ)⁻¹ * z * P μ) h
    simpa [xPlus, mul_assoc] using this
  have hinjMinus : Function.Injective (fun s : K => P μ * xMinus s * (P μ)⁻¹) := by
    intro s s' h
    refine Matrix.SpecialLinearGroup.transvection_injective (show (2 : Fin 3) ≠ 0 by decide) ?_
    have := congrArg (fun z => (P μ)⁻¹ * z * P μ) h
    simpa [xMinus, mul_assoc] using this
  constructor
  · constructor
    · intro hfix
      have h2 : P μ * xPlus (σ t) * (P μ)⁻¹ = P μ * xPlus t * (P μ)⁻¹ := by
        rw [← hpair.1]; exact hfix
      exact hinjPlus h2
    · intro hσt
      rw [hpair.1, hσt]
  · constructor
    · intro hfix
      have h2 : P μ * xMinus (σ t) * (P μ)⁻¹ = P μ * xMinus t * (P μ)⁻¹ := by
        rw [← hpair.2]; exact hfix
      exact hinjMinus h2
    · intro hσt
      rw [hpair.2, hσt]

end CharTwo

section Frobenius

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]

theorem exists_unitary_opposite_pair {f : ℕ} (hf : 1 ≤ f) (σ : Ω ≃+* Ω)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ∃ (F : Subfield Ω) (μ : Ω),
      (∀ c : Ω, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c) ∧
      Nat.card F = (2 ^ f) ^ 2 ∧
      μ ∈ F ∧
      μ + σ μ = 1 ∧
      (∀ t : Ω, stdUnitary σ.toRingHom (P μ * xPlus t * (P μ)⁻¹) =
        P μ * xPlus (σ t) * (P μ)⁻¹) ∧
      (∀ t : Ω, stdUnitary σ.toRingHom (P μ * xMinus t * (P μ)⁻¹) =
        P μ * xMinus (σ t) * (P μ)⁻¹) ∧
      (∀ t : Ω, P μ * xPlus t * (P μ)⁻¹ ∈ (statedSUToSL F 3 (2 ^ f)).range ↔
        t ^ (2 ^ f) = t) ∧
      (∀ t : Ω, P μ * xMinus t * (P μ)⁻¹ ∈ (statedSUToSL F 3 (2 ^ f)).range ↔
        t ^ (2 ^ f) = t) := by
  obtain ⟨F, hF, hFcard⟩ :=
    exists_subfield_card_sq (L := Ω) (ℓ := 2) (f := f) Nat.prime_two hf
  have hFcard' : Nat.card F = 2 ^ (2 * f) := by
    rw [hFcard, ← pow_mul, Nat.mul_comm f 2]
  let hdata : UnitaryFieldData 2 f F :=
    { prime := Nat.prime_two
      one_le := hf
      card := hFcard' }
  obtain ⟨μF, hμF⟩ := hdata.traceLin_surjective (1 : hdata.fixedField)
  have htrace : ((hdata.trace μF : F) : Ω) = 1 := by
    rw [← UnitaryFieldData.coe_traceLin, hμF]
    rfl
  have hsum : ((μF : F) : Ω) + ((hdata.bar μF : F) : Ω) = 1 := by
    simpa only [UnitaryFieldData.trace, Subfield.coe_add] using htrace
  have hbar : ((hdata.bar μF : F) : Ω) = σ ((μF : F) : Ω) := by
    rw [UnitaryFieldData.bar_apply]
    change (Subfield.subtype F) (μF ^ 2 ^ f) = σ ((Subfield.subtype F) μF)
    rw [map_pow, ← hσ]
  have hμ : ((μF : F) : Ω) + σ ((μF : F) : Ω) = 1 := by
    rw [← hbar]
    exact hsum
  refine ⟨F, (μF : Ω), hF, hFcard, μF.2, hμ, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (unitary_opposite_pair_formula (K := Ω) σ.toRingHom (μF : Ω) hμ t).1
  · intro t
    exact (unitary_opposite_pair_formula (K := Ω) σ.toRingHom (μF : Ω) hμ t).2
  · intro t
    have hmem : P ((μF : F) : Ω) * xPlus t * (P ((μF : F) : Ω))⁻¹ ∈
          (statedSUToSL F 3 (2 ^ f)).range ↔
        stdUnitary σ.toRingHom (P ((μF : F) : Ω) * xPlus t * (P ((μF : F) : Ω))⁻¹) =
          P ((μF : F) : Ω) * xPlus t * (P ((μF : F) : Ω))⁻¹ :=
      (mem_range_statedSUToSL_iff (ℓ := 2) (f := f) Nat.prime_two F hF hFcard
          (by norm_num) _).trans
        (stdUnitary_eq_self_iff (ℓ := 2) (f := f) σ hσ _).symm
    rw [hmem]
    refine ((unitary_opposite_pair_fixed_iff (K := Ω) σ.toRingHom (μF : Ω) hμ t).1).trans ?_
    rw [show σ.toRingHom t = t ^ 2 ^ f from hσ t]
  · intro t
    have hmem : P ((μF : F) : Ω) * xMinus t * (P ((μF : F) : Ω))⁻¹ ∈
          (statedSUToSL F 3 (2 ^ f)).range ↔
        stdUnitary σ.toRingHom (P ((μF : F) : Ω) * xMinus t * (P ((μF : F) : Ω))⁻¹) =
          P ((μF : F) : Ω) * xMinus t * (P ((μF : F) : Ω))⁻¹ :=
      (mem_range_statedSUToSL_iff (ℓ := 2) (f := f) Nat.prime_two F hF hFcard
          (by norm_num) _).trans
        (stdUnitary_eq_self_iff (ℓ := 2) (f := f) σ hσ _).symm
    rw [hmem]
    refine ((unitary_opposite_pair_fixed_iff (K := Ω) σ.toRingHom (μF : Ω) hμ t).2).trans ?_
    rw [show σ.toRingHom t = t ^ 2 ^ f from hσ t]

end Frobenius

theorem xPlus_eq_transvection (t : K) :
    xPlus t = Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t := by
  rw [xPlus]

theorem xMinus_eq_transvection (t : K) :
    xMinus t = Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t := by
  rw [xMinus]

end CFSG.StandardType.F4ExplicitPos.UnitaryPair

end

end
