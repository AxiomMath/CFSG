module

public import CFSG.LocalAnalysis.StandardType.GGTwE6A5KFrameDiag
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourToral
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenActs
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Steinberg.CentralExt.PerfectLift
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.RankThree.SubgroupLists2.SpectralBounds
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreHom
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenFrame
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenPin
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitType
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartOne.BRANCH.RankRee
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
import CFSG.RankThree.PartOne.KD4T.Certs
import CFSG.RankThree.PartOne.KE.StabGeneral
import CFSG.RankThree.PartOne.N143.Weyl613Defs
import CFSG.RankThree.PartOne.N143X.KF64WSimple
import CFSG.RankThree.PartOne.S11d.OutExceptional
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open scoped MatrixGroups Pointwise

private theorem exists_common_diag {Ω : Type} [Field Ω] [IsAlgClosed Ω] (h3 : ((3 : ℕ) : Ω) ≠ 0)
    {ι : Type*} (B : ι → GL (Fin 6) Ω)
    (hcube : ∀ x, ∃ μ : Ω, ((B x ^ 3 : GL (Fin 6) Ω) : Matrix (Fin 6) (Fin 6) Ω) = μ • 1)
    (hBc : ∀ x y, B x * B y = B y * B x) :
    ∃ S : SL(6, Ω), ∀ x i j, i ≠ j →
      ((↑S⁻¹ : Matrix (Fin 6) (Fin 6) Ω) * (B x : Matrix (Fin 6) (Fin 6) Ω) *
        (S : Matrix (Fin 6) (Fin 6) Ω)) i j = 0 := by
  have hl : ∀ x, ∃ l : Ω, l ≠ 0 ∧ (l • (B x : Matrix (Fin 6) (Fin 6) Ω)) ^ 3 = 1 := by
    intro x
    obtain ⟨μ, hμ⟩ := hcube x
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hμ
      exact Units.ne_zero _ hμ
    obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq μ⁻¹ (by norm_num : 0 < 3)
    refine ⟨l, ?_, ?_⟩
    · rintro rfl
      exact inv_ne_zero hμ0 (hl.symm.trans (zero_pow (by norm_num)))
    · rw [smul_pow, ← Units.val_pow_eq_pow_val, hμ, hl, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  choose l hl0 hl3 using hl
  obtain ⟨P, hP, d, hd⟩ := CFSG.RankThree.SubgroupLists.exists_simultaneous_diagonal
    (fun x => l x • (B x : Matrix (Fin 6) (Fin 6) Ω))
    (fun x y => by
      rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (l y), ← Units.val_mul,
        ← Units.val_mul, hBc x y])
    fun x => ⟨3, h3, hl3 x⟩
  have hdet : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).1 hP).ne_zero
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq P.det⁻¹ (by norm_num : 0 < 6)
  obtain ⟨S, hS⟩ : ∃ S : SL(6, Ω), (S : Matrix (Fin 6) (Fin 6) Ω) = c • P :=
    ⟨⟨c • P, by rw [Matrix.det_smul, Fintype.card_fin, hc, inv_mul_cancel₀ hdet]⟩, rfl⟩
  refine ⟨S, fun x i j hij => ?_⟩
  have hSS : (↑S⁻¹ : Matrix (Fin 6) (Fin 6) Ω) * (c • P) = 1 := by
    rw [← hS, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hd' : P * Matrix.diagonal (d x) = l x • ((B x : Matrix (Fin 6) (Fin 6) Ω) * P) := by
    rw [← hd x, Matrix.smul_mul]
  have key : l x • ((↑S⁻¹ : Matrix (Fin 6) (Fin 6) Ω) * (B x : Matrix (Fin 6) (Fin 6) Ω) *
      (S : Matrix (Fin 6) (Fin 6) Ω)) = Matrix.diagonal (d x) := by
    calc l x • ((↑S⁻¹ : Matrix (Fin 6) (Fin 6) Ω) * (B x : Matrix (Fin 6) (Fin 6) Ω) *
          (S : Matrix (Fin 6) (Fin 6) Ω))
        = (↑S⁻¹ : Matrix (Fin 6) (Fin 6) Ω) * (c • P) * Matrix.diagonal (d x) := by
          rw [Matrix.mul_assoc _ (c • P), Matrix.smul_mul, hd', hS]
          simp only [Matrix.mul_smul, Matrix.mul_assoc, smul_smul, mul_comm (l x) c]
      _ = Matrix.diagonal (d x) := by rw [hSS, Matrix.one_mul]
  have h := congrFun (congrFun key i) j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_ne _ hij] at h
  exact (mul_eq_zero.1 h).resolve_left (hl0 x)


private theorem frame_conj_scalar {Ω : Type} [Field Ω] {ψ : SL(6, Ω) →* ModGL Tag.E6 Ω}
    {σ' : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ') (M : GL (Fin 6) Ω)
    (h : ∀ Y, ψ (conjSLn M Y) = ψ Y) : ∃ c : Ω, (M : Matrix (Fin 6) (Fin 6) Ω) = c • 1 := by
  haveI : Group.IsPerfect SL(6, Ω) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  have hid : conjSLn M = MonoidHom.id SL(6, Ω) :=
    CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect
      (KSGen.frame_ker_le_center (by norm_num) hψ) (MonoidHom.ext fun Y => h Y)
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
    (M := (M : Matrix (Fin 6) (Fin 6) Ω)) fun i j hij => by
      have h1 := congrArg Subtype.val
        (DFunLike.congr_fun hid (Matrix.SpecialLinearGroup.transvection hij 1))
      rw [coe_conjSLn, MonoidHom.id_apply, CFSG.LinearGroups.coe_transvection] at h1
      have h2 : (M : Matrix (Fin 6) (Fin 6) Ω) * (1 + Matrix.single i j (1 : Ω)) =
          (1 + Matrix.single i j (1 : Ω)) * M := by
        conv_rhs => rw [← h1]
        rw [Matrix.mul_assoc _ _ (M : Matrix (Fin 6) (Fin 6) Ω), Units.inv_mul, Matrix.mul_one]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj] at h2
      exact h2.symm
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

private theorem torus_acts_diag {Ω : Type} [Field Ω] {ψ : SL(6, Ω) →* ModGL Tag.E6 Ω}
    {σ' : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ') {t : ModGL Tag.E6 Ω}
    (ht : t ∈ torusGroup Tag.E6 Ω) :
    ∃ e : Fin 6 → Ωˣ, ∀ Y, t * ψ Y * t⁻¹ = ψ (conjSLn (diagGLn e) Y) := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  exact ⟨_, fun Y => (hψ.torus 0 b Y).trans (congrArg ψ (KSGen.conjDiagn_eq_conjSLn _ Y))⟩

private theorem torus_le_normalizer {Ω : Type} [Field Ω] {ψ : SL(6, Ω) →* ModGL Tag.E6 Ω}
    {σ' : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ') :
    torusGroup Tag.E6 Ω ≤ Subgroup.normalizer (ψ.range : Set (ModGL Tag.E6 Ω)) := by
  have hc : ∀ t ∈ torusGroup Tag.E6 Ω, ∀ r ∈ ψ.range, t * r * t⁻¹ ∈ ψ.range := by
    rintro t ht _ ⟨Y, rfl⟩
    obtain ⟨e, he⟩ := torus_acts_diag hψ ht
    exact ⟨_, (he Y).symm⟩
  intro t ht
  refine Subgroup.mem_normalizer_iff.2 fun r => ⟨hc t ht r, fun hr => ?_⟩
  have := hc t⁻¹ (inv_mem ht) _ hr
  rwa [inv_inv, show t⁻¹ * (t * r * t⁻¹) * t = r by group] at this

private theorem mem_torus_of_acts_diag {Ω : Type} [Field Ω] {ψ : SL(6, Ω) →* ModGL Tag.E6 Ω}
    {σ' : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ') {x : ModGL Tag.E6 Ω}
    (hx : x ∈ torusGroup Tag.E6 Ω ⊔ ψ.range) (Δ : GL (Fin 6) Ω)
    (hΔ : ∀ i j, i ≠ j → (Δ : Matrix (Fin 6) (Fin 6) Ω) i j = 0)
    (hxΔ : ∀ Y, x * ψ Y * x⁻¹ = ψ (conjSLn Δ Y)) : x ∈ torusGroup Tag.E6 Ω := by
  have hx' : x ∈ (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) *
      (ψ.range : Set (ModGL Tag.E6 Ω)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (torus_le_normalizer hψ)]
    exact hx
  obtain ⟨t, ht, r, hr, rfl⟩ := Set.mem_mul.1 hx'
  obtain ⟨z, rfl⟩ := MonoidHom.mem_range.1 hr
  obtain ⟨e, he⟩ := torus_acts_diag hψ (inv_mem ht)
  obtain ⟨c, hc⟩ := frame_conj_scalar hψ
    (diagGLn e * Δ * (Matrix.SpecialLinearGroup.toGL z)⁻¹) fun W => by
      rw [KSGen.conjSLn_mul_apply, KSGen.conjSLn_mul_apply, ← he, ← hxΔ]
      have h1 : ψ z * ψ (conjSLn (Matrix.SpecialLinearGroup.toGL z)⁻¹ W) * (ψ z)⁻¹ = ψ W := by
        rw [← map_inv ψ, ← map_mul ψ, ← map_mul ψ, ← KSGen.conjSLn_toGL_apply,
          ← KSGen.conjSLn_mul_apply, mul_inv_cancel, KSGen.conjSLn_one_apply]
      rw [← h1]
      group
  have h2 : (diagGLn e : Matrix (Fin 6) (Fin 6) Ω) * Δ = c • (z : Matrix (Fin 6) (Fin 6) Ω) := by
    rw [← Units.val_mul,
      ← inv_mul_cancel_right (diagGLn e * Δ) (Matrix.SpecialLinearGroup.toGL z), Units.val_mul,
      hc, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.smul_mul, Matrix.one_mul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact Units.ne_zero _ hc
  have hz : z ∈ KSGen.diagSL 6 Ω := KSGen.mem_diagSL.2 fun i j hij => by
    have h3 := congrFun (congrFun h2 i) j
    rw [show (diagGLn e : Matrix (Fin 6) (Fin 6) Ω) = Matrix.diagonal fun k => (e k : Ω) from rfl,
      Matrix.diagonal_mul, hΔ i j hij, mul_zero, Matrix.smul_apply, smul_eq_mul] at h3
    exact (mul_eq_zero.1 h3.symm).resolve_left hc0
  exact mul_mem ht (frame_diagSL_mem_torusGroup hψ hz)

theorem e6AdToral_of_frame_commute {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (h3 : ((3 : ℕ) : Ω) ≠ 0) {ψ : SL(6, Ω) →* ModGL Tag.E6 Ω}
    {σ' : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ')
    {X : Subgroup (ModGL Tag.E6 Ω)} (hX : CFSG.Open.IsElemAbelian 3 X)
    (hXM : X ≤ torusGroup Tag.E6 Ω ⊔ ψ.range) (B : ModGL Tag.E6 Ω → GL (Fin 6) Ω)
    (hB : ∀ x ∈ X, ∀ Y : SL(6, Ω), x * ψ Y * x⁻¹ = ψ (conjSLn (B x) Y))
    (hBc : ∀ x ∈ X, ∀ y ∈ X, B x * B y = B y * B x) :
    E6AdToral X := by
  obtain ⟨-, hX3⟩ := hX
  have hcube : ∀ x ∈ X, ∃ μ : Ω, ((B x ^ 3 : GL (Fin 6) Ω) : Matrix (Fin 6) (Fin 6) Ω) = μ • 1 :=
    fun x hx => frame_conj_scalar hψ _ fun Y => by
      rw [pow_three, KSGen.conjSLn_mul_apply, KSGen.conjSLn_mul_apply, ← hB x hx, ← hB x hx,
        ← hB x hx]
      have hx3 : x * x * x = 1 := by rw [← pow_three']; exact hX3 x hx
      calc x * (x * (x * ψ Y * x⁻¹) * x⁻¹) * x⁻¹ = x * x * x * ψ Y * (x * x * x)⁻¹ := by
            simp only [mul_inv_rev, mul_assoc]
        _ = ψ Y := by rw [hx3, one_mul, inv_one, mul_one]
  obtain ⟨S, hS⟩ := exists_common_diag h3 (fun x : X => B x) (fun x => hcube x x.2)
    fun x y => hBc x x.2 y y.2
  refine ⟨(ψ S)⁻¹, inv_mem (hψ.range_le_adjointGroup ⟨S, rfl⟩), fun x hx => ?_⟩
  have hSM : ψ S ∈ torusGroup Tag.E6 Ω ⊔ ψ.range := Subgroup.mem_sup_right ⟨S, rfl⟩
  refine mem_torus_of_acts_diag hψ
    (mul_mem (mul_mem (inv_mem hSM) (hXM hx)) (inv_mem (inv_mem hSM)))
    ((Matrix.SpecialLinearGroup.toGL S)⁻¹ * B x * Matrix.SpecialLinearGroup.toGL S)
    (fun i j hij => ?_) fun Y => ?_
  · rw [Units.val_mul, Units.val_mul, ← map_inv Matrix.SpecialLinearGroup.toGL S,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact hS ⟨x, hx⟩ i j hij
  · rw [KSGen.conjSLn_mul_apply, KSGen.conjSLn_mul_apply,
      ← map_inv Matrix.SpecialLinearGroup.toGL S, KSGen.conjSLn_toGL_apply,
      KSGen.conjSLn_toGL_apply, map_mul ψ, map_mul ψ, ← hB x hx]
    simp only [map_mul, map_inv, inv_inv, mul_inv_rev]
    group

theorem exists_noncommuting_frame_matrices_of_not_toral {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (h3 : ((3 : ℕ) : Ω) ≠ 0) {ψ : SL(6, Ω) →* ModGL Tag.E6 Ω}
    {σ' : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ')
    {X : Subgroup (ModGL Tag.E6 Ω)} (hX : CFSG.Open.IsElemAbelian 3 X)
    (hXM : X ≤ torusGroup Tag.E6 Ω ⊔ ψ.range) (B : ModGL Tag.E6 Ω → GL (Fin 6) Ω)
    (hB : ∀ x ∈ X, ∀ Y : SL(6, Ω), x * ψ Y * x⁻¹ = ψ (conjSLn (B x) Y))
    (hNT : ¬ E6AdToral X) :
    ∃ x ∈ X, ∃ y ∈ X, B x * B y ≠ B y * B x := by
  by_contra hpair
  push Not at hpair
  exact hNT (e6AdToral_of_frame_commute h3 hψ hX hXM B hB hpair)

end CFSG.StandardType.SCFourCover
