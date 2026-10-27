module

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearBlocks
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapeSetup
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapeIso
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalTypes
import CFSG.LocalAnalysis.StandardType.GGPGLToralityEigenspace
import CFSG.LocalAnalysis.StandardType.GGAutomizerAbelianMatrix
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenKernel
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TTransfer
import CFSG.Open.StatedAPI
import CFSG.Blueprint.LieModelAPI
import CFSG.Blueprint.OddStandardExact
import CFSG.HardMathSupport.Dickson.DefCharOuter.Final
import CFSG.HardMathSupport.Dickson.KD.CharPAux.Exc
import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Defs
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Basic
import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Abs
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NInd
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
import CFSG.LocalAnalysis.GLTheoremA.PartI.I112CtxExt
import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat3
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndSwap
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphEnd
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KLR.Final
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item143N
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.Sec16.Item164Proof
import CFSG.RankThree.PartTwo.Sec16.Item169HJ
import CFSG.RankThree.PartTwo.Sec17.Item1724Two
import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
import CFSG.RankThree.PartTwo.Sec17.RouteProvers
import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
import CFSG.RankThree.S4Free.SuzukiEight
import Certificates.Certificate13659
import Certificates.Certificate13660
import Certificates.Certificate8137
import Certificates.Certificate8138
import Certificates.Certificate8140
import Certificates.Certificate8141
import Certificates.Certificate8166

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Polynomial CFSG.RankThree.PartOne.KCPrimary
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.StandardType.TablePThreeKG
open scoped commutatorElement

theorem exists_four_eigenspace_of_component_A3
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hKcard : Nat.card K = 2 ^ n) (hn3 : 3 ∣ 2 ^ n - 1)
    {d : GL (Fin 6) K} {δ : MulAut (PSLg 6 K)}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin 6) K))
      (fun h h' => (h' : GL (Fin 6) K) = d * h * d⁻¹) δ)
    (hd3 : d ^ 3 ∈ LargeEvenScalars (Fin 6) K)
    {J : Subgroup (PSLg 6 K)}
    (hJ : Assembly.IsComponentOf J (ggAutFixedSubgroup δ))
    (hlabel : GGHasLabel (⟨.A, 3, n⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J)) :
    ∃ lam : K, lam ≠ 0 ∧
      Module.finrank K
        (Module.End.eigenspace (glA d : Module.End K (Fin 6 → K)) lam) = 4 := by
  classical
  obtain ⟨h, hh, hgood, e, E, hEfield, hEfinite, hEchar, m, j, f,
      hm_eq, hj_eq, heJ, h1, h2, h3, h4, h5, h6, h8, h9, hf, hker⟩ :=
    linShape_setup (K := K) (N := 6) (inferInstance : CharP K 2) (by norm_num)
      (Or.inl (by rw [hKcard]; exact hn3)) hJ hd hd3
  letI : Field E := hEfield
  letI : Finite E := hEfinite
  letI : CharP E 2 := hEchar
  have hperfSL : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤ :=
    (isPerfect_specialLinearGroup m E h1 h2).commutator_eq_top
  obtain ⟨e1⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
      hperfSL f hf hker
  let e2 : Matrix.SpecialLinearGroup (Fin m) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) ≃*
      projectiveSL m E :=
    QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n := m) (K := E)).symm
  let ePSL : J ⧸ Subgroup.center J ≃* projectiveSL m E := e1.trans e2
  unfold GGHasLabel at hlabel
  dsimp only [LargeEvenRawDatum] at hlabel
  unfold LargeEvenRecipeLinear at hlabel
  obtain ⟨F, hFfield, hFfinite, hFcard, ⟨eF⟩⟩ := hlabel
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  have hcard_m : Nat.card (J ⧸ Subgroup.center J) =
      Nat.card (projectiveSL m E) :=
    Nat.card_congr ePSL.toEquiv
  have hcard_4 : Nat.card (J ⧸ Subgroup.center J) =
      Nat.card (projectiveSL (3 + 1) F) := by
    rw [Nat.card_congr eF.toEquiv]
    exact Nat.card_congr (TypeA.recipeEquiv (3 + 1) F).toEquiv
  have hEcard : Nat.card E = 2 ^ (n * j) := by
    rw [h5, hKcard, pow_mul]
  have hfac_m :
      (Nat.card (projectiveSL m E)).factorization 2 =
        (n * j) * (m * (m - 1) / 2) := by
    have hnpos : 0 < n := by omega
    have hjpos : 0 < j := by omega
    simpa only [mul_assoc] using
      (CFSG.SeitzReduction.LinearPilot.factorization_card_projectiveSL_two_pow
        (a := n * j) (K₀ := E) (n := m) (Nat.mul_pos hnpos hjpos) hEcard (by omega))
  have hfac_4 :
      (Nat.card (projectiveSL (3 + 1) F)).factorization 2 = n * 6 := by
    simpa using
      (CFSG.SeitzReduction.LinearPilot.factorization_card_projectiveSL_two_pow
        (a := n) (K₀ := F) (n := 3 + 1) hn hFcard (by norm_num))
  have hval : n * (j * (m * (m - 1) / 2)) = n * 6 := by
    calc n * (j * (m * (m - 1) / 2))
        = (n * j) * (m * (m - 1) / 2) := (mul_assoc n j _).symm
      _ = (Nat.card (projectiveSL m E)).factorization 2 := hfac_m.symm
      _ = (Nat.card (J ⧸ Subgroup.center J)).factorization 2 := by rw [hcard_m]
      _ = (Nat.card (projectiveSL (3 + 1) F)).factorization 2 := by rw [hcard_4]
      _ = n * 6 := hfac_4
  have hnpos : 0 < n := by omega
  have hjA : j * (m * (m - 1) / 2) = 6 :=
    Nat.eq_of_mul_eq_mul_left hnpos hval
  have hm6 : m ≤ 6 := by
    calc m = 1 * m := (one_mul m).symm
      _ ≤ j * m := Nat.mul_le_mul_right m h3
      _ ≤ 6 := h6
  have hj1 : j = 1 := by
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with hj | hj | hj
    · exact hj
    · exfalso
      have hK2 : Nat.card K = 2 := h9 hj
      have hpow : 2 ^ n = 2 ^ 1 := by
        rw [← hKcard]
        simpa using hK2
      have hn1 : n = 1 := Nat.pow_right_injective (le_refl 2) hpow
      rw [hn1] at hn3
      norm_num at hn3
    · exfalso
      have h6m : 6 = 3 * m := (h8 hj).2
      have hm2 : m = 2 := by omega
      rw [hj, hm2] at hjA
      norm_num at hjA
  have hm4 : m = 4 := by
    rw [hj1] at hjA
    interval_cases m <;> norm_num at hjA
    rfl
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hdeg1 : h.natDegree = 1 := by
    rw [← hj_eq]
    exact hj1
  have hform : h = X + C (h.coeff 0) := hmon.eq_X_add_C hdeg1
  let x : Module.End K (Fin 6 → K) := glA d
  have hxfour : Module.finrank K (primaryComponent x h) = 4 := by
    rw [finrank_primaryComponent]
    change h.natDegree * primaryMultiplicity (glA d : Module.End K (Fin 6 → K)) h = 4
    rw [hdeg1, one_mul, ← hm_eq, hm4]
  have hcomp : primaryComponent x h =
      Module.End.eigenspace x (-(h.coeff 0)) := by
    ext v
    rw [mem_primaryComponent, Module.End.mem_eigenspace_iff]
    conv_lhs => rw [hform]
    simp only [map_add, aeval_X, aeval_C, LinearMap.add_apply, Module.algebraMap_end_apply]
    constructor
    · intro h0
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left h0
    · intro h0
      rw [neg_smul] at h0
      rw [h0]
      simp
  have hfour : Module.finrank K (Module.End.eigenspace
      (glA d : Module.End K (Fin 6 → K)) (-(h.coeff 0))) = 4 := by
    have hx : Module.End.eigenspace (glA d : Module.End K (Fin 6 → K)) (-(h.coeff 0))
        = primaryComponent x h := hcomp.symm
    rw [hx]
    exact hxfour
  refine ⟨-(h.coeff 0), ?_, hfour⟩
  intro hlam0
  have hker_bot : LinearMap.ker (glA d : Module.End K (Fin 6 → K)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (LinearMap.GeneralLinearGroup.toLinearEquiv (glA d)).injective
  have hbot : Module.End.eigenspace (glA d : Module.End K (Fin 6 → K)) (-(h.coeff 0)) = ⊥ := by
    rw [hlam0, Module.End.eigenspace_zero]
    exact hker_bot
  have h4bot : Module.finrank K (⊥ : Submodule K (Fin 6 → K)) = 4 := by
    rw [← hbot]
    exact hfour
  simp at h4bot

theorem largeEvenLabelAll_A5_notDvdSCJ (n : ℕ) (hn : 1 ≤ n) (hp : 3 ∣ 2 ^ n - 1) :
    LargeEvenLabelAll ⟨.A, 5, n⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 (⟨.A, 3, n⟩ : LargeEvenLabel) R I 4 27 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hQ
  refine ⟨K, hKfield, hKfinite, hKcard, hQ, ?_⟩
  let U : Subgroup (GL (Fin 6) K) := LargeEvenSLGroup (Fin 6) K
  let N : Subgroup (GL (Fin 6) K) :=
    Subgroup.normalizer (U : Set (GL (Fin 6) K))
  let ρ : N →* MulAut (LargeEvenProj U) := TableB.projConj U
  change GGTorusAutNotDvdSCJ 3 (⟨.A, 3, n⟩ : LargeEvenLabel)
    (LargeEvenProj U) (LargeEvenMatConjImage (LargeEvenProjMk U) Set.univ) 4 27
  intro L' _ _ ψ hψ hker hperf A hA hAI _h3 _hle _hsc hcomp
  classical
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hKcard
  haveI hUnormal : U.Normal := by
    dsimp only [U]
    rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.statedSL_eq_ker_det]
    infer_instance
  have hNtop : N = ⊤ := by
    dsimp only [N]
    exact Subgroup.normalizer_eq_top U
  have hS : (Set.univ : Set (GL (Fin 6) K)) ⊆ N := by
    intro M _
    rw [hNtop]
    exact Subgroup.mem_top M
  have hscal : ρ.ker ≤
      (LargeEvenScalars (Fin 6) K).subgroupOf N := by
    intro X hX
    exact Subgroup.mem_subgroupOf.mpr
      (CFSG.LocalAnalysis.GLTheoremA.T171Sh.linKernelScalar_of_three_le
        (K := K) (N := 6) (by norm_num) X hX)
  obtain ⟨e, he, J', hJ', hlabel⟩ := hcomp
  obtain ⟨φ, hφI, hφe⟩ := hAI e he
  obtain ⟨M, _hM, hMeq⟩ :=
    TableB.exists_eq_projConj (H := U) (S := Set.univ) hS hφI
  let Mnorm : N := ⟨M, hS (Set.mem_univ M)⟩
  have hMeq' : φ = ρ Mnorm := by
    simpa [Mnorm] using hMeq
  let X : Subgroup (MulAut (LargeEvenProj U)) := TypeA.inducedSub ψ A
  have hX : IsElemAbelian 3 X := TypeA.isElemAbelian_inducedSub hψ hA
  have hφX : φ ∈ X := TypeA.mem_inducedSub.mpr ⟨e, he, hφe⟩
  have hφ3 : φ ^ 3 = 1 := hX.2 φ hφX
  have hM3ker : Mnorm ^ 3 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    change ρ (Mnorm ^ 3) = 1
    rw [map_pow, ← hMeq']
    exact hφ3
  have hd3 : M ^ 3 ∈ LargeEvenScalars (Fin 6) K := by
    have hsub := hscal hM3ker
    simpa [Mnorm, Subgroup.coe_pow] using Subgroup.mem_subgroupOf.mp hsub
  have hgraph : LargeEvenGraphAut (LargeEvenProjMk U)
      (fun h h' => (h' : GL (Fin 6) K) = M * h * M⁻¹) φ := by
    intro h h' hrel
    rw [hMeq']
    change (TableB.projConj U) Mnorm (h : LargeEvenProj U) =
      (h' : LargeEvenProj U)
    rw [TableB.projConj_mk]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hrel.symm
  have hJ'fix : Assembly.IsComponentOf J' (ggFix e) := by
    simpa only [ggFix, ggFixSub] using hJ'
  have hcompat : ∀ x : L', ψ (e x) = φ (ψ x) := fun x => (hφe x).symm
  have hJmapFix : Assembly.IsComponentOf (J'.map ψ) (ggFix φ) :=
    LayerCC.isComponentOf_map_ggFix hψ hker hcompat hJ'fix
  have hJ_R : Assembly.IsComponentOf (J'.map ψ) (ggAutFixedSubgroup φ) := by
    simpa only [ggAutFixedSubgroup, ggFix] using hJmapFix
  have hJperf : ⁅J', J'⁆ = J' := by
    have hperfClass : Group.IsPerfect ↥J' := ⟨hJ'.2.2.1⟩
    exact Subgroup.isPerfect_iff.mp hperfClass
  have hk : ∀ g : L', ψ g = 1 → g ∈ Subgroup.center L' := by
    intro g hg
    exact hker (by rw [MonoidHom.mem_ker]; exact hg)
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.I142T.nonempty_quot_center_equiv
    ψ hk hJperf
  have hlabelR : GGHasLabel (⟨.A, 3, n⟩ : LargeEvenLabel)
      ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ)) :=
    ggHasLabel_of_mulEquiv eJ hlabel
  obtain ⟨lam, hlam, hdim⟩ :=
    exists_four_eigenspace_of_component_A3 (K := K) (n := n) hn hKcard hp
      (d := M) (δ := φ) hgraph hd3 hJ_R hlabelR
  have hmul : (M : Matrix (Fin 6) (Fin 6) K).mulVecLin =
      Matrix.toLin' (M : Matrix (Fin 6) (Fin 6) K) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.mulVecLin_apply, Matrix.toLin'_apply]
  have hgl : (glA M : Module.End K (Fin 6 → K)) =
      (M : Matrix (Fin 6) (Fin 6) K).mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [glA, Matrix.GeneralLinearGroup.toLin_apply]
  have hdim' : Module.finrank K
      (Module.End.eigenspace (Matrix.toLin' (M : Matrix (Fin 6) (Fin 6) K)) lam) = 4 := by
    rw [← hmul, ← hgl]
    exact hdim
  have hNscal : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 6) u ∈ N := by
    intro u
    exact TableB.scalar_mem_normalizer U (by
      rw [largeEvenScalars_def]
      exact MonoidHom.mem_range.mpr ⟨u, rfl⟩)
  have hρscal : ∀ u : Kˣ, ρ ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) u, hNscal u⟩ = 1 := by
    intro u
    simpa using TableB.projConj_of_scalar U (by
      rw [largeEvenScalars_def]
      exact MonoidHom.mem_range.mpr ⟨u, rfl⟩)
  have hE : M ∈ (X.comap ρ).map N.subtype := by
    refine Subgroup.mem_map.mpr ⟨Mnorm, ?_, rfl⟩
    rw [Subgroup.mem_comap, ← hMeq']
    exact hφX
  have hBcommGL : ∀ g ∈ (X.comap ρ).map N.subtype,
      ∀ h ∈ (X.comap ρ).map N.subtype, g * h = h * g :=
    TypeA.PGLTor.pairwise_commute_of_isElemAbelian_comap_map_of_eigenspace_four
      hNscal hρscal hscal hX hE hlam hdim'
  have hBcomm : ∀ b ∈ fullMatrixPreimage U ψ A,
      ∀ c ∈ fullMatrixPreimage U ψ A, b * c = c * b := by
    intro b hb c hc
    apply Subtype.ext
    exact hBcommGL (b : GL (Fin 6) K)
      (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
      (c : GL (Fin 6) K) (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)
  have hdvd : Nat.card
      (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∣ Nat.factorial 6 :=
    card_ggAutomizer_dvd_factorial_of_matConjImage_elemAbelian
      (d := 6) (by norm_num) (U := U) ψ hψ hker hperf hA hscal hS hAI hBcomm
  rw [show Nat.factorial 6 = 720 by norm_num] at hdvd
  intro h27
  exact (by norm_num : ¬ 27 ∣ 720) (h27.trans hdvd)

end CFSG.StandardType

end
