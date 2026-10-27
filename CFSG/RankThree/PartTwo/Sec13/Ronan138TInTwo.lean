module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138TInType
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKTwoMat
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKTwoType
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKTwo
import CFSG.RankThree.PartTwo.Sec13.Ronan138SRefl
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.PartTwo.KFacts.K71Basic
import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.ClassTwoEightActionInverting
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartOne.KF.LayerCover
import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofTools
import CFSG.RankThree.PartTwo.Sec4.LThreePiIrred
import Mathlib.Tactic.FinCases
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
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
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofCenter
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import Certificates.Certificate43
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138T

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi zPi PiField ModThree ModNine IsTypeC Type123 qSubPi
  diagE blockHom coe_blockHom blockMat)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open Matrix
open Ronan138S (mem_centralizer_of_mk_conj_pi perfectResidual_centralizer_conj_pi
  eq_one_of_mem_block_of_mk_eq_one inf_centralizer_conj_pi det_blockHom)
open scoped commutatorElement

section Mat

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem pow_three_eq_one_of_type1 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {N : GL (Fin 3) K} (hN : N ∈ slPi π 3 (p ^ f) K) (h1 : Type123 π (p ^ f) K N 1) :
    N ^ 3 = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1, z, hz, g, -, hD⟩ := h1
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hK hq
  obtain ⟨l, rfl⟩ := Sec4.mem_statedScalars_of_mem_zPi hK hq hτ₀ hτ₀1 hz
  have hNz : N * GeneralLinearGroup.scalar (Fin 3) l = g * Sec4.diagTau hτ * g⁻¹ := by
    rw [← hD]
    group
  have hl3 : l ^ 3 = 1 := by
    have h1 := congrArg GeneralLinearGroup.det hNz
    have hdN : GeneralLinearGroup.det N = 1 := by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, Units.val_one]
      exact ((Sec4.mem_slPi_iff hπ).mp hN).2
    have hdT : GeneralLinearGroup.det (Sec4.diagTau hτ) = 1 := by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, Units.val_one, Sec4.coe_diagTau_eq_diagonal,
        Matrix.det_diagonal, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      linear_combination hτ
    rw [map_mul, map_mul, map_mul, hdN, one_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      hdT, mul_one, mul_comm, map_inv, inv_mul_cancel] at h1
    exact h1
  have h3 : (N * GeneralLinearGroup.scalar (Fin 3) l) ^ 3 = 1 := by
    rw [hNz, conj_pow, Sec4.diagTau_pow_three hτ, mul_one, mul_inv_cancel]
  rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar l N).mul_pow, ← map_pow, hl3,
    map_one, mul_one] at h3
  exact h3

theorem exists_mem_block_of_pow_three (hK : PiField π p f K) {e₀ : Kˣ} (he₀ : e₀ ≠ 1)
    {g N : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hN : N ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {g * diagE e₀ * g⁻¹})
    (hN3 : N ^ 3 = 1) :
    ∃ N'' ∈ ((slPi π 2 (p ^ f) K).map blockHom).map (MulAut.conj g).toMonoidHom,
      ProjGenLinGroup.mk N'' = ProjGenLinGroup.mk N := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rw [inf_centralizer_conj_pi hK hg, Sec4.centralizer_diagE_eq hK he₀] at hN
  obtain ⟨M, ⟨B, hB, rfl⟩, rfl⟩ := hN
  have h1 : blockHom (B ^ 3) = 1 := by
    have h2 : (MulAut.conj g).toMonoidHom (blockHom (B ^ 3)) = 1 := by
      rw [map_pow, map_pow]
      exact hN3
    have h3 : g * blockHom (B ^ 3) * g⁻¹ = 1 := h2
    calc blockHom (B ^ 3) = g⁻¹ * (g * blockHom (B ^ 3) * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  have hB3 : GeneralLinearGroup.det B ^ 3 = 1 := by
    have h00 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [coe_blockHom, Units.val_one] at h00
    have h4 : (((GeneralLinearGroup.det (B ^ 3))⁻¹ : Kˣ) : K) = 1 := by
      simpa [blockMat] using h00
    have h5 : (GeneralLinearGroup.det (B ^ 3))⁻¹ = 1 := Units.ext h4
    rw [inv_eq_one, map_pow] at h5
    exact h5
  obtain ⟨δ, hδ⟩ : ∃ δ : Kˣ, GeneralLinearGroup.det B = δ := ⟨_, rfl⟩
  have hδμ : δ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := hδ ▸ Ronan138S.det_mem_rootsOfUnity_two hK hB
  have hδ3 : δ ^ 3 = 1 := hδ ▸ hB3
  obtain ⟨B'', hB''⟩ : ∃ B'' : GL (Fin 2) K, B'' = GeneralLinearGroup.scalar (Fin 2) δ * B :=
    ⟨_, rfl⟩
  have hdet'' : GeneralLinearGroup.det B'' = 1 := by
    rw [hB'', map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, hδ, ← pow_succ]
    exact hδ3
  have hB''S : B'' ∈ slPi π 2 (p ^ f) K := (Sec4.mem_slPi_iff hπ).mpr
    ⟨hB'' ▸ mul_mem (Ronan138S.scalar_two_mem_glPi hK hδμ) hB, by
      rw [← GeneralLinearGroup.val_det_apply, hdet'', Units.val_one]⟩
  have hB''m : ((B'' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (δ : K) • (B : Matrix (Fin 2) (Fin 2) K) := by
    rw [hB'', Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have hblock : blockHom B'' = GeneralLinearGroup.scalar (Fin 3) δ * blockHom B := by
    apply Units.ext
    rw [coe_blockHom, hdet'', inv_one, Units.val_one, hB''m]
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_blockHom, hδ]
    have hδ0 : (δ : K) ≠ 0 := δ.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMat, Matrix.scalar_apply, Matrix.diagonal, Matrix.mul_apply, hδ0]
  refine ⟨(MulAut.conj g).toMonoidHom (blockHom B''),
    Subgroup.mem_map_of_mem _ ⟨B'', hB''S, rfl⟩, ?_⟩
  have hconj : (MulAut.conj g).toMonoidHom (GeneralLinearGroup.scalar (Fin 3) δ) =
      GeneralLinearGroup.scalar (Fin 3) δ := by
    change g * _ * g⁻¹ = _
    rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar δ g).eq, mul_inv_cancel_right]
  rw [hblock, map_mul (MulAut.conj g).toMonoidHom, hconj, map_mul, ProjGenLinGroup.mk_scalar,
    one_mul]

end Mat

theorem typeTwo_frame {G : Type} [Group G] [Finite G] {A L E F : Subgroup G} {c x y t : G}
    (hfr : Ronan138S.Frame138Base A L E F c x y t) {e : G} (heE : e ∈ E) (heF : e ∉ F) :
    ⁅x, y⁆ ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) ∧
      IsQuasisimple (↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G))) ⧸
        aschbacherSolvableCore 3
          ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH := hfr.hH
  obtain ⟨h, -, hcE, hE3, -, hEN, hCE, -, hC⟩ := hH
  obtain ⟨π, p, f, K, _, hK, hq, φ, D, hD, hτD, -⟩ := hC
  have hL := h.mem_thetaComponentsAt
  have hq2 := Item138Proof.two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL)
    hK hq φ
  have he : e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers ⁅x, y⁆ := fun h' => heF
    ((sup_le (Subgroup.zpowers_le.mpr hfr.hcF)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hfr.hdZ).2)) h')
  have hd1T := fun N hN hNd => type1_of_lift_d hfr hK hq φ (N := N) hN hNd
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hx : e ∈ Subgroup.normalizer (L : Set G) := hEN heE
  obtain ⟨yM, hyD, hy⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨e, hx, heE, rfl⟩)
  have hy2 := type2_of_not_mem_zpowers h hEN hCE hfr.hdE hfr.hdL hfr.hd1 hK hq φ hd1T hD hτD heE
    he hyD hy
  have : Finite K := hK.finite
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨e₀, he₀3, he₀1, z, hz, g, hg, hD2⟩ := hy2
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  obtain ⟨ζ, -, rfl⟩ := Sec4.exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
  set y₀ := g * Sec4.diagE e₀ * g⁻¹ with hy₀
  have hyy₀ : ProjGenLinGroup.mk yM = ProjGenLinGroup.mk y₀ := by
    have h1 : yM * GeneralLinearGroup.scalar (Fin 3) ζ = y₀ := by rw [hy₀, ← hD2]; group
    rw [← h1, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  have : Finite (GL (Fin 3) K) := inferInstance
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  set S : Subgroup (projImage (slPi π 3 (p ^ f) K)) :=
    fixedSubgroupOf (KFacts.inducedAutHom L φ ⟨e, hx⟩) with hS
  have hSmem : ∀ w : projImage (slPi π 3 (p ^ f) K),
      w ∈ S ↔ KFacts.inducedAutHom L φ ⟨e, hx⟩ w = w :=
    fun w => mem_fixedSubgroupOf _ w
  have hind : ∀ w : projImage (slPi π 3 (p ^ f) K),
      ((KFacts.inducedAutHom L φ ⟨e, hx⟩ w : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk y₀ * (w : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y₀)⁻¹ := by
    intro w
    have h1 := hy (φ.symm w)
    rw [MulEquiv.apply_symm_apply, hyy₀] at h1
    rw [KFacts.inducedAutHom_apply, MulAut.congr_apply]
    exact h1
  set T := (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y₀}).map ProjGenLinGroup.mk with hT
  have hST : S.map (projImage (slPi π 3 (p ^ f) K)).subtype = T := by
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨N, hN, hNs⟩ := s.2
      have h1 := hind s
      rw [(hSmem s).mp hs] at h1
      refine ⟨N, ⟨hN, ?_⟩, hNs⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (mem_centralizer_of_mk_conj_pi hK he₀3 h3 hg hN (by rw [hNs]; exact h1.symm))
    · rintro ⟨N, ⟨hN, hNc⟩, rfl⟩
      have hNM : ProjGenLinGroup.mk N ∈ projImage (slPi π 3 (p ^ f) K) := ⟨N, hN, rfl⟩
      refine ⟨⟨_, hNM⟩, (hSmem _).mpr ?_, rfl⟩
      apply Subtype.ext
      rw [hind]
      have hNc' : N * y₀ = y₀ * N := Subgroup.mem_centralizer_singleton_iff.mp hNc
      change ProjGenLinGroup.mk y₀ * ProjGenLinGroup.mk N * (ProjGenLinGroup.mk y₀)⁻¹ =
        ProjGenLinGroup.mk N
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [← hNc']
      group
  set I := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) with hI
  have hx3' : ∃ j : ℕ, e ^ 3 ^ j = 1 := ⟨1, by simpa using hE3.2 e heE⟩
  have hĪ := KFacts.imageModTheta_perfectResidual_centralizer_eq hx hx3'
  have hB := KFacts.map_barCentralizer_eq hx φ S hSmem
  set ψ : (L ⧸ aschbacherSolvableCore 3 L) →* ProjGenLinGroup (Fin 3) K :=
    (projImage (slPi π 3 (p ^ f) K)).subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ :=
    (projImage (slPi π 3 (p ^ f) K)).subtype_injective.comp φ.injective
  set Λ := ((slPi π 2 (p ^ f) K).map Sec4.blockHom).map (MulAut.conj g).toMonoidHom with hΛ
  have hΛ' : (Sec8.imageModTheta L I).map ψ = Λ.map ProjGenLinGroup.mk := by
    rw [hĪ, hψ, ← Subgroup.map_map, CFSG.RankThree.PartTwo.map_inSubgroup_perfectResidual, hB,
      GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
        (projImage (slPi π 3 (p ^ f) K)).subtype_injective,
      hST, hT, ← PartOne.KFU.map_inSubgroup_perfectResidual,
      perfectResidual_centralizer_conj_pi hK hq hq2 he₀1 hg]
  have hmkinj : Function.Injective (ProjGenLinGroup.mk.comp Λ.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro N hN
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hN
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_mem_block_of_mk_eq_one hK N.2 hN)
  have hrange : (ProjGenLinGroup.mk.comp Λ.subtype).range = Λ.map ProjGenLinGroup.mk := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eΛ : Λ ≃* Λ.map (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K) :=
    (MonoidHom.ofInjective hmkinj).trans (MulEquiv.subgroupCongr hrange)
  let eSL : slPi π 2 (p ^ f) K ≃* Λ :=
    ((slPi π 2 (p ^ f) K).equivMapOfInjective _ Sec4.blockHom_injective).trans
      (((slPi π 2 (p ^ f) K).map Sec4.blockHom).equivMapOfInjective _
        (MulAut.conj g).injective)
  let eĪ : Sec8.imageModTheta L I ≃* slPi π 2 (p ^ f) K :=
    ((Sec8.imageModTheta L I).equivMapOfInjective ψ hψinj).trans
      ((MulEquiv.subgroupCongr hΛ').trans (eΛ.symm.trans eSL.symm))
  have hĪq : IsQuasisimple (Sec8.imageModTheta L I) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eĪ.symm
      (Sec11.KS11LieProof.isQuasisimple_slPi_two hK hq hq2)
  have hIL : I ≤ L := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  let ρ : I →* Sec8.imageModTheta L I :=
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hIL)).codRestrict
      _ (fun i => ⟨Subgroup.inclusion hIL i, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨w, l, hl, rfl⟩
    refine ⟨⟨l, Subgroup.mem_subgroupOf.mp hl⟩, ?_⟩
    apply Subtype.ext
    rfl
  obtain ⟨hθs, hθ3⟩ := Sec6.theta_solvable_and_not_dvd L
  obtain ⟨hks, hk3⟩ := Sec13.ker_facts_of_injective ρ I.subtype I.subtype_injective
    (inSubgroup (aschbacherSolvableCore 3) L) (fun i hi => by
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (Subgroup.inclusion hIL i) = 1 :=
        congrArg Subtype.val hi
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩) hθs hθ3
  have hIq := Sec14.isQuasisimple_quotient_theta_of_surjective hĪq ρ hρ hks hk3
  refine ⟨?_, hIq⟩
  set d := ⁅x, y⁆ with hd
  have hdE : d ∈ E := hfr.hdE
  have hdL : d ∈ L := hfr.hdL
  have hd3 : d ^ 3 = 1 := hE3.2 d hdE
  have hxd : e * d = d * e := hEc e heE d hdE
  set D' : L ⧸ aschbacherSolvableCore 3 L :=
    ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) with hD'
  have hD'B : D' ∈ Sec8.barCentralizer (Subgroup.zpowers e) L := by
    rw [KFacts.mem_barCentralizer_zpowers_iff hx, hD', Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    show e * d * e⁻¹ = d
    rw [hxd, mul_inv_cancel_right]
  have heD'S : φ D' ∈ S := by
    rw [← hB]
    exact ⟨D', hD'B, rfl⟩
  have heD'T : ψ D' ∈ T := by
    rw [← hST]
    exact ⟨_, heD'S, rfl⟩
  obtain ⟨N, hN, hND⟩ := heD'T
  have hD3 : D' ^ 3 = 1 := by
    rw [hD', ← QuotientGroup.mk_pow]
    have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, QuotientGroup.mk_one]
  have hN3 : N ^ 3 = 1 := pow_three_eq_one_of_type1 hK hq hN.1
    (hd1T N hN.1 (hND.trans rfl))
  obtain ⟨N'', hN''Λ, hN''⟩ := exists_mem_block_of_pow_three hK he₀1 hg hN hN3
  have hD'Ī : D' ∈ Sec8.imageModTheta L I := by
    have h1 : ψ D' ∈ (Sec8.imageModTheta L I).map ψ := by
      rw [hΛ']
      exact ⟨N'', hN''Λ, hN''.trans hND⟩
    obtain ⟨w, hw, hwD⟩ := h1
    rwa [hψinj hwD] at hw
  obtain ⟨l, hl, hlD⟩ := hD'Ī
  have hlI : (l : G) ∈ I := Subgroup.mem_subgroupOf.mp hl
  have hθ' : (l : G)⁻¹ * d ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have h1 : ((l : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := hlD
    rw [QuotientGroup.eq] at h1
    exact ⟨_, h1, rfl⟩
  have hdC : d ∈ L ⊓ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hdL, Subgroup.mem_centralizer_singleton_iff.mpr hxd.symm⟩
  have hdNI : d ∈ Subgroup.normalizer (I : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (Subgroup.le_normalizer hdC)
  have hord : Nat.Coprime (orderOf ((l : G)⁻¹ * d)) 3 := by
    have hdvd := Subgroup.orderOf_dvd_natCard _ hθ'
    have hcop : Nat.Coprime 3 (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
    exact (hcop.symm.coprime_dvd_left hdvd)
  exact Sec8.Item812Res2.mem_of_mul_mem_of_coprime hd3 hdNI hlI (by group) hord

end CFSG.RankThree.PartTwo.Sec13.Ronan138T
