module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.UnitaryDiagonal
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUAniso
import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDet
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CGT.Timmesfeld75.Cfg214Gen
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CharacterTheory.Semidihedral.ElementStructure
import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
import CFSG.ClassicalInvolution.Generic.InductionMain
import CFSG.ClassicalInvolution.ModelFacts.OddCover
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.Models.Transfer
import CFSG.ClassicalInvolution.Models.UnitaryFrames
import CFSG.ClassicalInvolution.Models.UnitaryPairs
import CFSG.ClassicalInvolution.RouteD.TypeAChain
import CFSG.Foundations
import CFSG.LargeExtraspecial.S9TIXC
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LieType.SeitzGeneration.HyperLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.RankThreeUC.Asc1930
import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder
import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.LocalAnalysis.WeakClosure81.FiveFive
import CFSG.Quasithin.Background.A1bGroups
import CFSG.RankThree.PartOne.CTP.SeitzUIndex
import CFSG.RankThree.PartOne.CTP.StrongPFinal
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import Certificates.Certificate18000
import Certificates.Certificate4058
import Certificates.Certificate4058Base
import Certificates.Certificate4071
import Certificates.Certificate4082
import Certificates.Certificate4083
import Certificates.Certificate4083Base
import Certificates.Certificate8032
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.Unitary

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

private lemma exists_unitaryInvolution (h : UnitaryFieldData p f K) :
    ∃ σ : K ≃+* K, IsUnitaryInvolution σ ∧ ∀ c, σ c = h.bar c := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  exact ⟨CFSG.LieType.BorelTits.unitaryInvolution K p f,
    isUnitaryInvolution_unitaryInvolution h.card_eq_sq, fun c => by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]⟩

private lemma gramForm_one_eq_herm (h : UnitaryFieldData p f K) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = h.bar c) (x y : Fin n → K) :
    gramForm h (1 : Matrix (Fin n) (Fin n) K) x y = herm σ x y := by
  rw [gramForm_apply, herm_def, Matrix.one_mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [hσ]

private lemma herm_toLin {h : UnitaryFieldData p f K} {σ : K ≃+* K}
    (hσ : ∀ c, σ c = h.bar c) {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∀ x y, herm σ (Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) x)
      (Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) y) = herm σ x y := by
  intro x y
  have h1 := gramForm_mulVec h (1 : Matrix (Fin n) (Fin n) K) (A : Matrix (Fin n) (Fin n) K) x y
  have hA' : ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * 1 * (A : Matrix (Fin n) (Fin n) K) =
      1 := by
    simpa using mem_primeFormUnitary.mp hA
  rw [hA'] at h1
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← gramForm_one_eq_herm h hσ,
    ← gramForm_one_eq_herm h hσ]
  exact h1

private lemma bar_mul_self_of_sq_scalar (h : UnitaryFieldData p f K) (hn : 0 < n)
    {M : Matrix (Fin n) (Fin n) K} (hM : (M.map h.bar)ᵀ * M = 1) {α : K}
    (hM2 : M * M = α • 1) : h.bar α * α = 1 := by
  have h1 : α • (M.map h.bar)ᵀ = M := by
    calc α • (M.map h.bar)ᵀ = (M.map h.bar)ᵀ * (α • (1 : Matrix (Fin n) (Fin n) K)) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
      _ = (M.map h.bar)ᵀ * (M * M) := by rw [hM2]
      _ = ((M.map h.bar)ᵀ * M) * M := by rw [Matrix.mul_assoc]
      _ = M := by rw [hM, Matrix.one_mul]
  have h2 : α • (M.map h.bar) = Mᵀ := by
    have := congrArg Matrix.transpose h1
    simpa [Matrix.transpose_smul] using this
  have h3 : h.bar α • M = (M.map h.bar)ᵀ := by
    have hmap := congrArg (fun N => N.map h.bar) h2
    rw [Matrix.map_smul' h.bar α _ (map_mul h.bar), Matrix.map_map, Matrix.transpose_map] at hmap
    have hcomp : (⇑h.bar ∘ ⇑h.bar) = id := funext h.bar_bar
    rw [hcomp, Matrix.map_id] at hmap
    exact hmap
  have h4 : h.bar α • (M * M) = 1 := by
    rw [← Matrix.smul_mul, h3, hM]
  have h5 : (h.bar α * α) • (1 : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [hM2, smul_smul] at h4
    exact h4
  have h6 := congrFun (congrFun h5 ⟨0, hn⟩) ⟨0, hn⟩
  simpa [Matrix.smul_apply, Matrix.one_apply] using h6

private lemma neg_one_ne_one_of_two_ne_zero (h2 : (2 : K) ≠ 0) : (-1 : K) ≠ 1 := by
  intro h
  have h' : (1 : K) + 1 = 0 := (neg_eq_iff_add_eq_zero).mp h
  exact h2 (by rw [show (2 : K) = 1 + 1 by norm_num]; exact h')

private lemma eigenspace_sup_of_sq {T : Module.End K (Fin n → K)} (h2 : (2 : K) ≠ 0) {γ : K}
    (hγ : γ ≠ 0) (hT : ∀ v, T (T v) = (γ * γ) • v) :
    T.eigenspace γ ⊔ T.eigenspace (-γ) = ⊤ := by
  have h2γ : (2 : K) * γ ≠ 0 := mul_ne_zero h2 hγ
  rw [eq_top_iff]
  intro v _
  refine Submodule.mem_sup.2 ⟨((2 * γ)⁻¹) • (T v + γ • v), ?_,
    ((2 * γ)⁻¹) • (γ • v - T v), ?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, map_smul, map_add, map_smul, hT]
    generalize h : T v = y
    match_scalars <;> field_simp
  · rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, map_smul, hT]
    generalize h : T v = y
    match_scalars <;> field_simp
  · rw [← smul_add]
    have hsum : (T v + γ • v) + (γ • v - T v) = (2 * γ) • v := by
      rw [two_mul, add_smul]
      abel
    rw [hsum, smul_smul, inv_mul_cancel₀ h2γ, one_smul]

private lemma eigenspace_inf_of_sq {T : Module.End K (Fin n → K)} (h2 : (2 : K) ≠ 0) {γ : K}
    (hγ : γ ≠ 0) : T.eigenspace γ ⊓ T.eigenspace (-γ) = ⊥ := by
  rw [eq_bot_iff]
  intro v hvv
  obtain ⟨hv, hv'⟩ := Submodule.mem_inf.1 hvv
  rw [Module.End.mem_eigenspace_iff] at hv hv'
  have h4 : γ • v = (-γ) • v := by rw [← hv, hv']
  rw [neg_smul] at h4
  have h3 : γ • v + γ • v = 0 := by
    nth_rewrite 1 [h4]
    rw [neg_add_cancel]
  rw [← add_smul, ← two_mul] at h3
  exact (Submodule.mem_bot K).2
    ((smul_eq_zero.1 h3).resolve_left (mul_ne_zero h2 hγ))

private lemma isCompl_eigenspace_of_sq {T : Module.End K (Fin n → K)} (h2 : (2 : K) ≠ 0)
    {γ : K} (hγ : γ ≠ 0) (hT : ∀ v, T (T v) = (γ * γ) • v) :
    IsCompl (T.eigenspace γ) (T.eigenspace (-γ)) :=
  ⟨disjoint_iff.mpr (eigenspace_inf_of_sq h2 hγ),
    codisjoint_iff.mpr (eigenspace_sup_of_sq h2 hγ hT)⟩

private lemma herm_eigenspace_orth {σ : K ≃+* K} {T : Module.End K (Fin n → K)}
    (hT : ∀ x y, herm σ (T x) (T y) = herm σ x y) {lam mu : K} (hne : σ lam * mu ≠ 1)
    {u w : Fin n → K} (hu : u ∈ T.eigenspace lam) (hw : w ∈ T.eigenspace mu) :
    herm σ u w = 0 := by
  have h := hT u w
  rw [Module.End.mem_eigenspace_iff] at hu hw
  rw [hu, hw, herm_smul_left, herm_smul_right] at h
  have h' : (σ lam * mu - 1) * herm σ u w = 0 := by linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hne)

private lemma eigenspace_disjoint {T : Module.End K (Fin n → K)} {lam mu : K} (h : lam ≠ mu) :
    Disjoint (T.eigenspace lam) (T.eigenspace mu) := by
  rw [disjoint_iff_inf_le]
  intro v hv
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
  rw [Module.End.mem_eigenspace_iff] at h1 h2
  have h3 : (lam - mu) • v = 0 := by rw [sub_smul, ← h1, ← h2, sub_self]
  exact (Submodule.mem_bot K).2 ((smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 h))

private lemma eigenspace_split {U : Module.End K (Fin n → K)} {t : K}
    (h2 : (2 : K) ≠ 0) (ht : t ≠ 0) (hU2 : ∀ v, U (U v) = (t * t) • v)
    {W : Submodule K (Fin n → K)} (hW : ∀ v ∈ W, U v ∈ W) :
    W = (W ⊓ U.eigenspace t) ⊔ (W ⊓ U.eigenspace (-t)) := by
  have ht2 : (2 : K) * t ≠ 0 := mul_ne_zero h2 ht
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro v hv
  have hu : U v ∈ W := hW v hv
  refine Submodule.mem_sup.2 ⟨((2 * t)⁻¹) • (t • v + U v), ?_,
    ((2 * t)⁻¹) • (t • v - U v), ?_, ?_⟩
  · refine Submodule.mem_inf.2 ⟨W.smul_mem _ (W.add_mem (W.smul_mem _ hv) hu), ?_⟩
    rw [Module.End.mem_eigenspace_iff, map_smul, map_add, map_smul, hU2]
    generalize h : U v = y
    match_scalars <;> field_simp
  · refine Submodule.mem_inf.2 ⟨W.smul_mem _ (W.sub_mem (W.smul_mem _ hv) hu), ?_⟩
    rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, map_smul, hU2]
    generalize h : U v = y
    match_scalars <;> field_simp
  · generalize h : U v = y
    match_scalars <;> field_simp <;> norm_num

private lemma finrank_le_of_mapsTo {T : Module.End K (Fin n → K)} (hT : Function.Injective T)
    {P Q : Submodule K (Fin n → K)} (h : ∀ v ∈ P, T v ∈ Q) :
    Module.finrank K P ≤ Module.finrank K Q :=
  LinearMap.finrank_le_finrank_of_injective (f := T.restrict h) fun a b hab => by
    apply Subtype.ext
    exact hT (congrArg Subtype.val hab)

private lemma span_pair_stable {σ : K ≃+* K} {T U : Module.End K (Fin n → K)} {u : Fin n → K}
    (hu0 : u ≠ 0)
    {γ μ β : K} (hTu : T u = γ • u) (hTUu : T (U u) = μ • (U u)) (hU2 : ∀ v, U (U v) = β • v)
    (hUU : herm σ (U u) (U u) = 0) (huu : herm σ u u = 0) (huU : herm σ u (U u) = 0)
    (hUu : herm σ (U u) u = 0) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
      (∀ w ∈ W, T w ∈ W) ∧ ∀ w ∈ W, U w ∈ W := by
  refine ⟨Submodule.span K {u, U u}, ?_, ?_, ?_, ?_⟩
  · intro h
    have : u ∈ Submodule.span K {u, U u} := Submodule.subset_span (by simp)
    rw [h] at this
    exact hu0 ((Submodule.mem_bot K).1 this)
  · intro x hx y hy
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hx
    obtain ⟨c', d', rfl⟩ := Submodule.mem_span_pair.1 hy
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
    rw [huu, huU, hUU, hUu]
    ring
  · intro w hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hw
    refine Submodule.mem_span_pair.2 ⟨c * γ, d * μ, ?_⟩
    rw [map_add, map_smul, map_smul, hTu, hTUu, smul_smul, smul_smul]
  · intro w hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hw
    refine Submodule.mem_span_pair.2 ⟨d * β, c, ?_⟩
    rw [map_add, map_smul, map_smul, hU2, smul_smul]
    exact add_comm _ _

private lemma stable_of_anticomm {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0)
    (hn : 3 ≤ n)
    {T U : Module.End K (Fin n → K)} {γ β : K}
    (hT : ∀ x y, herm σ (T x) (T y) = herm σ x y)
    (hU : ∀ x y, herm σ (U x) (U y) = herm σ x y) (hUinj : Function.Injective U)
    (hγ : γ ≠ 0) (hε : σ γ * γ = 1 ∨ σ γ * γ = -1)
    (hT2 : ∀ v, T (T v) = (γ * γ) • v) (hU2 : ∀ v, U (U v) = β • v)
    (hanti : ∀ v, T (U v) = -(U (T v))) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
      (∀ w ∈ W, T w ∈ W) ∧ ∀ w ∈ W, U w ∈ W := by
  have hn0 : 0 < n := by omega
  have hcompl := isCompl_eigenspace_of_sq h2 hγ hT2
  have hTU : ∀ u ∈ T.eigenspace γ, U u ∈ T.eigenspace (-γ) := fun u hu => by
    rw [Module.End.mem_eigenspace_iff] at hu ⊢
    rw [hanti, hu, map_smul, neg_smul]
  have hUT : ∀ u ∈ T.eigenspace (-γ), U u ∈ T.eigenspace γ := fun u hu => by
    rw [Module.End.mem_eigenspace_iff] at hu ⊢
    rw [hanti, hu, map_smul, neg_smul, neg_neg]
  have hdim : 2 ≤ Module.finrank K (T.eigenspace γ) := by
    have hle1 := finrank_le_of_mapsTo hUinj hTU
    have hle2 := finrank_le_of_mapsTo hUinj hUT
    have h1 : Module.finrank K (T.eigenspace γ) + Module.finrank K (T.eigenspace (-γ)) = n := by
      rw [Submodule.finrank_add_eq_of_isCompl hcompl, Module.finrank_fin_fun]
    omega
  have key : ∀ u ∈ T.eigenspace γ, u ≠ 0 → herm σ u u = 0 → herm σ u (U u) = 0 →
      ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
        (∀ w ∈ W, T w ∈ W) ∧ ∀ w ∈ W, U w ∈ W := fun u hu hu0 huu huU =>
    span_pair_stable hu0 (Module.End.mem_eigenspace_iff.mp hu)
      (Module.End.mem_eigenspace_iff.mp (hTU u hu)) hU2 (by rw [hU u u, huu])
      huu huU (herm_eq_zero_comm σ hσ.invol huU)
  rcases hε with hε | hε
  · obtain ⟨u, hu, hu0, huu⟩ := USeitz.exists_isotropic_of_two_le hσ hdim LinearMap.id
      (fun x y => herm_conj σ hσ.invol x y)
    exact key u hu hu0 huu (herm_eigenspace_orth hT
      (by rw [mul_neg, hε]; exact neg_one_ne_one_of_two_ne_zero h2) hu (hTU u hu))
  · have hβ : σ β * β = 1 := by
      have hv : herm σ (Pi.single ⟨0, hn0⟩ (1 : K)) (Pi.single ⟨0, hn0⟩ 1) = 1 := by
        rw [herm_single_left, Pi.single_eq_same, map_one, one_mul]
      have h1 := hU (U (Pi.single ⟨0, hn0⟩ (1 : K))) (U (Pi.single ⟨0, hn0⟩ (1 : K)))
      have hUe : herm σ (U (Pi.single ⟨0, hn0⟩ (1 : K))) (U (Pi.single ⟨0, hn0⟩ (1 : K))) = 1 := by
        rw [hU, hv]
      rw [hU2, herm_smul_left, herm_smul_right, hv, mul_one, hUe] at h1
      exact h1
    obtain ⟨ρ, hρ0, hρ⟩ := USeitz.exists_hilbert90 hσ h2 (α := σ β)
      (by rw [hσ.invol, mul_comm]; exact hβ)
    obtain ⟨u, hu, hu0, hub⟩ := USeitz.exists_isotropic_of_two_le hσ hdim (ρ • U) fun x y => by
      simp only [LinearMap.smul_apply, herm_smul_right, map_mul]
      rw [← herm_conj σ hσ.invol x (U y), ← hU y (U x), hU2, herm_smul_right]
      have hρ' : σ ρ = β * ρ := by
        have h := congrArg σ hρ
        rw [map_mul] at h
        rw [hσ.invol, hσ.invol] at h
        exact h.symm
      rw [hρ']
      ring
    refine key u hu hu0 (herm_eigenspace_orth hT
      (by rw [hε]; exact neg_one_ne_one_of_two_ne_zero h2) hu hu) ?_
    simpa [LinearMap.smul_apply, hρ0] using hub

private lemma stable_of_comm_anti {σ : K ≃+* K} (h2 : (2 : K) ≠ 0) (hn : 1 ≤ n)
    {T U : Module.End K (Fin n → K)} {γ : K}
    (hT : ∀ x y, herm σ (T x) (T y) = herm σ x y) (hγ : γ ≠ 0)
    (hε : σ γ * γ = -1) (hT2 : ∀ v, T (T v) = (γ * γ) • v)
    (hcomm : ∀ v, T (U v) = U (T v)) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
      (∀ w ∈ W, T w ∈ W) ∧ ∀ w ∈ W, U w ∈ W := by
  have hcompl := isCompl_eigenspace_of_sq h2 hγ hT2
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have key : ∀ μ : K, σ μ * μ = -1 → T.eigenspace μ ≠ ⊥ →
      ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
        (∀ w ∈ W, T w ∈ W) ∧ ∀ w ∈ W, U w ∈ W := fun μ hμ hne =>
    ⟨T.eigenspace μ, hne, fun x hx y hy =>
      herm_eigenspace_orth hT (by rw [hμ]; exact neg_one_ne_one_of_two_ne_zero h2) hx hy,
      fun w hw => by
        rw [Module.End.mem_eigenspace_iff.mp hw]; exact Submodule.smul_mem _ μ hw,
      fun w hw => by
        rw [Module.End.mem_eigenspace_iff, hcomm, Module.End.mem_eigenspace_iff.mp hw,
          map_smul]⟩
  by_cases hp : T.eigenspace γ = ⊥
  · refine key (-γ) (by rw [map_neg, neg_mul_neg]; exact hε) fun hm => ?_
    have h := hcompl.codisjoint.eq_top
    rw [hp, hm, bot_sup_eq] at h
    exact bot_ne_top h
  · exact key γ hε hp

private lemma comm_line {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    {T U : Module.End K (Fin n → K)} {V : Submodule K (Fin n → K)} {lam mu : K}
    (hV : V ≤ T.eigenspace lam) (hV' : V ≤ U.eigenspace mu) (h2 : 2 ≤ Module.finrank K V) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
      (∀ w ∈ W, T w ∈ W) ∧ ∀ w ∈ W, U w ∈ W := by
  obtain ⟨w, hw, hw0, hww⟩ := USeitz.exists_isotropic_of_two_le hσ h2 LinearMap.id
    (fun x y => herm_conj σ hσ.invol x y)
  refine ⟨Submodule.span K {w}, ?_, ?_, ?_, ?_⟩
  · intro hbot
    have : w ∈ Submodule.span K {w} := Submodule.subset_span (by simp)
    rw [hbot] at this
    exact hw0 ((Submodule.mem_bot K).1 this)
  · intro x hx y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hww' : herm σ w w = 0 := by simpa using hww
    rw [herm_smul_left, herm_smul_right, hww', mul_zero, mul_zero]
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine Submodule.mem_span_singleton.2 ⟨c * lam, ?_⟩
    rw [map_smul, Module.End.mem_eigenspace_iff.mp (hV hw), smul_smul]
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine Submodule.mem_span_singleton.2 ⟨c * mu, ?_⟩
    rw [map_smul, Module.End.mem_eigenspace_iff.mp (hV' hw), smul_smul]

private lemma det_eq_pow_mul_pow {T : Module.End K (Fin n → K)} {γ : K}
    (h2 : (2 : K) ≠ 0) (hγ : γ ≠ 0) (hT2 : ∀ v, T (T v) = (γ * γ) • v) :
    LinearMap.det T = γ ^ Module.finrank K (T.eigenspace γ) *
      (-γ) ^ Module.finrank K (T.eigenspace (-γ)) := by
  classical
  have hcompl := isCompl_eigenspace_of_sq h2 hγ hT2
  have hP : ∀ v ∈ T.eigenspace γ, T v ∈ T.eigenspace γ := by
    intro v hv
    have hv' := Module.End.mem_eigenspace_iff.mp hv
    rw [Module.End.mem_eigenspace_iff, hv', map_smul, hv']
  have hQ : ∀ v ∈ T.eigenspace (-γ), T v ∈ T.eigenspace (-γ) := by
    intro v hv
    have hv' := Module.End.mem_eigenspace_iff.mp hv
    rw [Module.End.mem_eigenspace_iff, hv', map_smul, hv']
  have h1 : T.restrict hP = γ • (1 : Module.End K (T.eigenspace γ)) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [LinearMap.restrict_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Module.End.mem_eigenspace_iff.mp v.2
  have h2' : T.restrict hQ = (-γ) • (1 : Module.End K (T.eigenspace (-γ))) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [LinearMap.restrict_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Module.End.mem_eigenspace_iff.mp v.2
  have hdet := CFSG.RankThree.PartOne.KCUnitary.det_eq_mul_det_of_isCompl hcompl T hP hQ
  rw [h1, h2'] at hdet
  simpa using hdet

private lemma exists_det_smul_eq_one_of_sq_three {h : UnitaryFieldData p f K} {x : K}
    (hx : h.norm x = 1) (hx0 : x ≠ 0) {X : Matrix (Fin 3) (Fin 3) K}
    (hd : X.det ^ 2 = (x ^ 3) ^ 2) :
    ∃ c : K, h.norm c = 1 ∧ (c • X).det = 1 := by
  have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx0
  have hε : X.det = x ^ 3 ∨ X.det = -(x ^ 3) := by
    have h : (X.det / x ^ 3) * (X.det / x ^ 3) = 1 := by
      rw [← sq, div_pow, hd, div_self (pow_ne_zero 2 hx3)]
    rcases mul_self_eq_one_iff.mp h with h | h
    · left; rw [div_eq_one_iff_eq hx3] at h; exact h
    · right; rw [div_eq_iff hx3] at h; simpa using h
  rcases hε with hpos | hneg
  · refine ⟨x⁻¹, ?_, ?_⟩
    · rw [norm_inv_eq, hx, inv_one]
    · rw [Matrix.det_smul, hpos, Fintype.card_fin, ← mul_pow, inv_mul_cancel₀ hx0, one_pow]
  · refine ⟨-(x⁻¹), ?_, ?_⟩
    · rw [show (-(x⁻¹) : K) = -1 * x⁻¹ by ring, norm_mul_eq]
      rw [show h.norm (-1 : K) = 1 by
        show (-1 : K) * h.bar (-1) = 1; simp]
      rw [norm_inv_eq, hx, inv_one, mul_one]
    · rw [Matrix.det_smul, hneg, Fintype.card_fin]
      have hcube : (-(x⁻¹)) ^ 3 = -(x⁻¹) ^ 3 := by ring
      rw [hcube]
      field_simp

private lemma exists_det_smul_eq_one_of_det_pow {h : UnitaryFieldData p f K} {x : K}
    (hx : h.norm x = 1) (hx0 : x ≠ 0) {X : Matrix (Fin 4) (Fin 4) K} (hd : X.det = x ^ 4) :
    ∃ c : K, h.norm c = 1 ∧ (c • X).det = 1 := by
  refine ⟨x⁻¹, ?_, ?_⟩
  · rw [norm_inv_eq, hx, inv_one]
  · rw [Matrix.det_smul, hd, Fintype.card_fin]
    field_simp

private lemma stable_isotropic_of_sq_scalar (h : UnitaryFieldData p f K) {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) (hσbar : ∀ c, σ c = h.bar c) (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    {Ma Mb : Matrix (Fin n) (Fin n) K} {α β : K}
    (hMa : ∀ x y, herm σ (Ma *ᵥ x) (Ma *ᵥ y) = herm σ x y)
    (hMb : ∀ x y, herm σ (Mb *ᵥ x) (Mb *ᵥ y) = herm σ x y)
    (hA2 : Ma * Ma = α • 1) (hB2 : Mb * Mb = β • 1)
    (hAB : Ma * Mb = Mb * Ma ∨ Ma * Mb = -(Mb * Ma))
    (hout : ¬ ((∃ c : K, h.norm c = 1 ∧ (c • Ma).det = 1) ∧
      (∃ c : K, h.norm c = 1 ∧ (c • Mb).det = 1) ∧
      (∃ c : K, h.norm c = 1 ∧ (c • (Ma * Mb)).det = 1))) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
      (∀ w ∈ W, Ma *ᵥ w ∈ W) ∧ ∀ w ∈ W, Mb *ᵥ w ∈ W := by
  have : Finite K := h.finite
  have hMa' : (Ma.map h.bar)ᵀ * Ma = 1 := by
    have h1 : ∀ x y, gramForm h (1 : Matrix (Fin n) (Fin n) K) (Ma *ᵥ x) (Ma *ᵥ y) =
        gramForm h 1 x y := by
      intro x y
      rw [gramForm_one_eq_herm h hσbar, gramForm_one_eq_herm h hσbar]
      exact hMa x y
    have := (gramForm_isometry_iff h (1 : Matrix (Fin n) (Fin n) K) Ma).mp h1
    simpa using this
  have hMb' : (Mb.map h.bar)ᵀ * Mb = 1 := by
    have h1 : ∀ x y, gramForm h (1 : Matrix (Fin n) (Fin n) K) (Mb *ᵥ x) (Mb *ᵥ y) =
        gramForm h 1 x y := by
      intro x y
      rw [gramForm_one_eq_herm h hσbar, gramForm_one_eq_herm h hσbar]
      exact hMb x y
    have := (gramForm_isometry_iff h (1 : Matrix (Fin n) (Fin n) K) Mb).mp h1
    simpa using this
  have hα : σ α * α = 1 := by
    rw [hσbar]; exact bar_mul_self_of_sq_scalar h (by omega) hMa' hA2
  obtain ⟨s, hs⟩ := USeitz.exists_sq_of_norm_one hσ h2 hα
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hs
    rw [← hs] at hα
    simp at hα
  have hβ : σ β * β = 1 := by
    rw [hσbar]; exact bar_mul_self_of_sq_scalar h (by omega) hMb' hB2
  obtain ⟨t, ht⟩ := USeitz.exists_sq_of_norm_one hσ h2 hβ
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at ht
    rw [← ht] at hβ
    simp at hβ
  set T : Module.End K (Fin n → K) := Matrix.toLin' Ma with hT
  set U : Module.End K (Fin n → K) := Matrix.toLin' Mb with hU
  have hTapp : ∀ v, T v = Ma *ᵥ v := fun v => by rw [hT]; exact Matrix.toLin'_apply Ma v
  have hUapp : ∀ v, U v = Mb *ᵥ v := fun v => by rw [hU]; exact Matrix.toLin'_apply Mb v
  have hTiso : ∀ x y, herm σ (T x) (T y) = herm σ x y := fun x y => by
    rw [hTapp, hTapp]; exact hMa x y
  have hUiso : ∀ x y, herm σ (U x) (U y) = herm σ x y := fun x y => by
    rw [hUapp, hUapp]; exact hMb x y
  have hTinj : Function.Injective T := fun a b hab => by
    have h1 : Ma *ᵥ a = Ma *ᵥ b := by rw [← hTapp a, ← hTapp b]; exact hab
    have h2 : (Ma.map h.bar)ᵀ *ᵥ (Ma *ᵥ a) = (Ma.map h.bar)ᵀ *ᵥ (Ma *ᵥ b) := by rw [h1]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMa', Matrix.one_mulVec,
      Matrix.one_mulVec] at h2
  have hUinj : Function.Injective U := fun a b hab => by
    have h1 : Mb *ᵥ a = Mb *ᵥ b := by rw [← hUapp a, ← hUapp b]; exact hab
    have h2 : (Mb.map h.bar)ᵀ *ᵥ (Mb *ᵥ a) = (Mb.map h.bar)ᵀ *ᵥ (Mb *ᵥ b) := by rw [h1]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMb', Matrix.one_mulVec,
      Matrix.one_mulVec] at h2
  have hT2 : ∀ v, T (T v) = (s * s) • v := by
    intro v
    have h1 : Ma *ᵥ (Ma *ᵥ v) = (s * s) • v := by
      rw [Matrix.mulVec_mulVec, hA2, ← hs, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hTapp, hTapp, h1]
  have hU2 : ∀ v, U (U v) = (t * t) • v := by
    intro v
    have h1 : Mb *ᵥ (Mb *ᵥ v) = (t * t) • v := by
      rw [Matrix.mulVec_mulVec, hB2, ← ht, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hUapp, hUapp, h1]
  have hεs : σ s * s = 1 ∨ σ s * s = -1 := by
    have hsquare : (σ s * s) * (σ s * s) = 1 := by
      rw [mul_mul_mul_comm, ← map_mul, hs, hα]
    exact mul_self_eq_one_iff.mp hsquare
  have hεt : σ t * t = 1 ∨ σ t * t = -1 := by
    have hsquare : (σ t * t) * (σ t * t) = 1 := by
      rw [mul_mul_mul_comm, ← map_mul, ht, hβ]
    exact mul_self_eq_one_iff.mp hsquare
  rcases hAB with hcomm | hanti
  · have hcommE : ∀ v, U (T v) = T (U v) := by
      intro v
      rw [hUapp, hTapp, hUapp, hTapp, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm]
    rcases hεs with hεs | hεs
    · rcases hεt with hεt | hεt
      ·
        have hNs : h.norm s = 1 := by
          show s * h.bar s = 1
          rw [mul_comm, ← hσbar]
          exact hεs
        have hNt : h.norm t = 1 := by
          show t * h.bar t = 1
          rw [mul_comm, ← hσbar]
          exact hεt
        have hNst : h.norm (s * t) = 1 := by rw [norm_mul_eq, hNs, hNt, one_mul]
        have hst0 : s * t ≠ 0 := mul_ne_zero hs0 ht0
        have hst_ne : s ≠ -s := by
          intro he
          have h2s : (2 : K) * s = 0 := by
            rw [two_mul]
            exact (eq_neg_iff_add_eq_zero).mp he
          exact (mul_ne_zero h2 hs0) h2s
        have htt_ne : t ≠ -t := by
          intro he
          have h2t : (2 : K) * t = 0 := by
            rw [two_mul]
            exact (eq_neg_iff_add_eq_zero).mp he
          exact (mul_ne_zero h2 ht0) h2t
        set V1 : Submodule K (Fin n → K) := T.eigenspace s ⊓ U.eigenspace t with hV1
        set V2 : Submodule K (Fin n → K) := T.eigenspace s ⊓ U.eigenspace (-t) with hV2
        set V3 : Submodule K (Fin n → K) := T.eigenspace (-s) ⊓ U.eigenspace t with hV3
        set V4 : Submodule K (Fin n → K) := T.eigenspace (-s) ⊓ U.eigenspace (-t) with hV4
        have hV12 : V1 ⊓ V2 = ⊥ := by
          refine le_bot_iff.1 ?_
          calc V1 ⊓ V2 ≤ U.eigenspace t ⊓ U.eigenspace (-t) := by
                rw [hV1, hV2]
                exact inf_le_inf inf_le_right inf_le_right
            _ = ⊥ := (eigenspace_disjoint htt_ne).eq_bot
        have hV34 : V3 ⊓ V4 = ⊥ := by
          refine le_bot_iff.1 ?_
          calc V3 ⊓ V4 ≤ U.eigenspace t ⊓ U.eigenspace (-t) := by
                rw [hV3, hV4]
                exact inf_le_inf inf_le_right inf_le_right
            _ = ⊥ := (eigenspace_disjoint htt_ne).eq_bot
        have hV13 : V1 ⊓ V3 = ⊥ := by
          refine le_bot_iff.1 ?_
          calc V1 ⊓ V3 ≤ T.eigenspace s ⊓ T.eigenspace (-s) := by
                rw [hV1, hV3]
                exact inf_le_inf inf_le_left inf_le_left
            _ = ⊥ := (eigenspace_disjoint hst_ne).eq_bot
        have hV24 : V2 ⊓ V4 = ⊥ := by
          refine le_bot_iff.1 ?_
          calc V2 ⊓ V4 ≤ T.eigenspace s ⊓ T.eigenspace (-s) := by
                rw [hV2, hV4]
                exact inf_le_inf inf_le_left inf_le_left
            _ = ⊥ := (eigenspace_disjoint hst_ne).eq_bot
        have hV23 : V2 ⊓ V3 = ⊥ := by
          refine le_bot_iff.1 ?_
          calc V2 ⊓ V3 ≤ U.eigenspace (-t) ⊓ U.eigenspace t := by
                rw [hV2, hV3]
                exact inf_le_inf inf_le_right inf_le_right
            _ = ⊥ := by rw [inf_comm]; exact (eigenspace_disjoint htt_ne).eq_bot
        have hV14 : V1 ⊓ V4 = ⊥ := by
          refine le_bot_iff.1 ?_
          calc V1 ⊓ V4 ≤ U.eigenspace t ⊓ U.eigenspace (-t) := by
                rw [hV1, hV4]
                exact inf_le_inf inf_le_right inf_le_right
            _ = ⊥ := (eigenspace_disjoint htt_ne).eq_bot
        have hsplitT : T.eigenspace s = V1 ⊔ V2 := by
          have hUT' : ∀ v ∈ T.eigenspace s, U v ∈ T.eigenspace s := by
            intro v hv
            rw [Module.End.mem_eigenspace_iff] at hv ⊢
            rw [← hcommE, hv, map_smul]
          have h := eigenspace_split (U := U) h2 ht0 hU2 hUT'
          rw [hV1, hV2]
          exact h
        have hsplitM : T.eigenspace (-s) = V3 ⊔ V4 := by
          have hUT' : ∀ v ∈ T.eigenspace (-s), U v ∈ T.eigenspace (-s) := by
            intro v hv
            rw [Module.End.mem_eigenspace_iff] at hv ⊢
            rw [← hcommE, hv, map_smul]
          have h := eigenspace_split (U := U) h2 ht0 hU2 hUT'
          rw [hV3, hV4]
          exact h
        have hsplitUt : U.eigenspace t = V1 ⊔ V3 := by
          have hTU' : ∀ v ∈ U.eigenspace t, T v ∈ U.eigenspace t := by
            intro v hv
            rw [Module.End.mem_eigenspace_iff] at hv ⊢
            rw [hcommE, hv, map_smul]
          have h := eigenspace_split (U := T) h2 hs0 hT2 hTU'
          simpa only [hV1, hV3, inf_comm] using h
        have hsplitUm : U.eigenspace (-t) = V2 ⊔ V4 := by
          have hTU' : ∀ v ∈ U.eigenspace (-t), T v ∈ U.eigenspace (-t) := by
            intro v hv
            rw [Module.End.mem_eigenspace_iff] at hv ⊢
            rw [hcommE, hv, map_smul]
          have h := eigenspace_split (U := T) h2 hs0 hT2 hTU'
          simpa only [hV2, hV4, inf_comm] using h
        have hd1 : Module.finrank K (T.eigenspace s) =
            Module.finrank K V1 + Module.finrank K V2 := by
          rw [hsplitT]
          have h := Submodule.finrank_sup_add_finrank_inf_eq V1 V2
          rw [hV12, finrank_bot, add_zero] at h
          exact h
        have hd2 : Module.finrank K (T.eigenspace (-s)) =
            Module.finrank K V3 + Module.finrank K V4 := by
          rw [hsplitM]
          have h := Submodule.finrank_sup_add_finrank_inf_eq V3 V4
          rw [hV34, finrank_bot, add_zero] at h
          exact h
        have hsum : Module.finrank K (T.eigenspace s) +
            Module.finrank K (T.eigenspace (-s)) = n := by
          rw [Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspace_of_sq h2 hs0 hT2),
            Module.finrank_fin_fun]
        have hsumU : Module.finrank K (U.eigenspace t) +
            Module.finrank K (U.eigenspace (-t)) = n := by
          rw [Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspace_of_sq h2 ht0 hU2),
            Module.finrank_fin_fun]
        by_cases hbig : 2 ≤ Module.finrank K V1 ∨ 2 ≤ Module.finrank K V2 ∨
            2 ≤ Module.finrank K V3 ∨ 2 ≤ Module.finrank K V4
        · rcases hbig with hbig | hbig | hbig | hbig
          · exact comm_line hσ (V := V1) (lam := s) (mu := t)
              (by rw [hV1]; exact inf_le_left) (by rw [hV1]; exact inf_le_right) hbig
          · exact comm_line hσ (V := V2) (lam := s) (mu := -t)
              (by rw [hV2]; exact inf_le_left) (by rw [hV2]; exact inf_le_right) hbig
          · exact comm_line hσ (V := V3) (lam := -s) (mu := t)
              (by rw [hV3]; exact inf_le_left) (by rw [hV3]; exact inf_le_right) hbig
          · exact comm_line hσ (V := V4) (lam := -s) (mu := -t)
              (by rw [hV4]; exact inf_le_left) (by rw [hV4]; exact inf_le_right) hbig
        ·
          have hle1 : Module.finrank K V1 ≤ 1 := by omega
          have hle2 : Module.finrank K V2 ≤ 1 := by omega
          have hle3 : Module.finrank K V3 ≤ 1 := by omega
          have hle4 : Module.finrank K V4 ≤ 1 := by omega
          have hle1' : Module.finrank K V1 ≤ 1 := hle1
          have hn34 : n = 3 ∨ n = 4 := by omega
          have hE2c : ∀ v, (T.comp U) ((T.comp U) v) = ((s * t) * (s * t)) • v := by
            intro v
            simp only [LinearMap.comp_apply]
            rw [hcommE, hU2, map_smul, map_smul, hT2, smul_smul]
            congr 1
            ring
          have hlin : Matrix.toLin' (Ma * Mb) = T.comp U := by
            rw [Matrix.toLin'_mul, ← hT, ← hU]
          have hAB2 : (Ma * Mb) * (Ma * Mb) = ((s * t) * (s * t)) • 1 := by
            apply Matrix.toLin'.injective
            rw [Matrix.toLin'_mul, hlin, Matrix.toLin'.map_smul, Matrix.toLin'_one]
            apply LinearMap.ext
            intro v
            exact hE2c v
          rcases hn34 with hn3 | hn4
          · subst hn3
            have hdA : Ma.det ^ 2 = (s ^ 3) ^ 2 := by
              have hdet := congrArg Matrix.det hA2
              rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, Matrix.det_one,
                mul_one] at hdet
              rw [pow_two, hdet, pow_two, ← hs]
              ring
            have hdB : Mb.det ^ 2 = (t ^ 3) ^ 2 := by
              have hdet := congrArg Matrix.det hB2
              rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, Matrix.det_one,
                mul_one] at hdet
              rw [pow_two, hdet, pow_two, ← ht]
              ring
            have hdAB : (Ma * Mb).det ^ 2 = ((s * t) ^ 3) ^ 2 := by
              have hdet := congrArg Matrix.det hAB2
              rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, Matrix.det_one,
                mul_one] at hdet
              rw [pow_two, hdet, pow_two]
              ring
            exact absurd ⟨exists_det_smul_eq_one_of_sq_three hNs hs0 hdA,
              exists_det_smul_eq_one_of_sq_three hNt ht0 hdB,
              exists_det_smul_eq_one_of_sq_three hNst hst0 hdAB⟩ hout
          · subst hn4
            have hV1f : Module.finrank K V1 = 1 := by omega
            have hV2f : Module.finrank K V2 = 1 := by omega
            have hV3f : Module.finrank K V3 = 1 := by omega
            have hV4f : Module.finrank K V4 = 1 := by omega
            have hdA : Ma.det = s ^ 4 := by
              have hbal : Module.finrank K (T.eigenspace (-s)) = 2 := by
                rw [hd2, hV3f, hV4f]
              have hdet := det_eq_pow_mul_pow (T := T) h2 hs0 hT2
              rw [hd1, hV1f, hV2f, hbal] at hdet
              rw [← LinearMap.det_toLin', ← hT, hdet]
              ring
            have hdB : Mb.det = t ^ 4 := by
              have hbal : Module.finrank K (U.eigenspace (-t)) = 2 := by
                rw [hsplitUm]
                have h := Submodule.finrank_sup_add_finrank_inf_eq V2 V4
                rw [hV24, finrank_bot, add_zero] at h
                omega
              have hbal2 : Module.finrank K (U.eigenspace t) = 2 := by
                rw [hsplitUt]
                have h := Submodule.finrank_sup_add_finrank_inf_eq V1 V3
                rw [hV13, finrank_bot, add_zero] at h
                omega
              have hdet := det_eq_pow_mul_pow (T := U) h2 ht0 hU2
              rw [hbal2, hbal] at hdet
              rw [← LinearMap.det_toLin', ← hU, hdet]
              ring
            have hincl1 : V1 ⊔ V4 ≤ Module.End.eigenspace (T.comp U) (s * t) := by
              refine sup_le ?_ ?_
              · intro v hv
                rw [hV1, Submodule.mem_inf] at hv
                obtain ⟨hv1, hv2⟩ := hv
                rw [Module.End.mem_eigenspace_iff] at hv1 hv2 ⊢
                rw [LinearMap.comp_apply, hv2, map_smul, hv1, smul_smul]
                congr 1
                ring
              · intro v hv
                rw [hV4, Submodule.mem_inf] at hv
                obtain ⟨hv1, hv2⟩ := hv
                rw [Module.End.mem_eigenspace_iff] at hv1 hv2 ⊢
                rw [LinearMap.comp_apply, hv2, map_smul, hv1, smul_smul]
                congr 1
                ring
            have hincl2 : V2 ⊔ V3 ≤ Module.End.eigenspace (T.comp U) (-(s * t)) := by
              refine sup_le ?_ ?_
              · intro v hv
                rw [hV2, Submodule.mem_inf] at hv
                obtain ⟨hv1, hv2⟩ := hv
                rw [Module.End.mem_eigenspace_iff] at hv1 hv2 ⊢
                rw [LinearMap.comp_apply, hv2, map_smul, hv1, smul_smul]
                congr 1
                ring
              · intro v hv
                rw [hV3, Submodule.mem_inf] at hv
                obtain ⟨hv1, hv2⟩ := hv
                rw [Module.End.mem_eigenspace_iff] at hv1 hv2 ⊢
                rw [LinearMap.comp_apply, hv2, map_smul, hv1, smul_smul]
                congr 1
                ring
            have hfr1 : 2 ≤ Module.finrank K (Module.End.eigenspace (T.comp U) (s * t)) := by
              have h := Submodule.finrank_strictMono.monotone hincl1
              have h1 : Module.finrank K ↥(V1 ⊔ V4) = 2 := by
                have h := Submodule.finrank_sup_add_finrank_inf_eq V1 V4
                rw [hV14, finrank_bot, add_zero] at h
                omega
              rwa [h1] at h
            have hfr2 : 2 ≤ Module.finrank K (Module.End.eigenspace (T.comp U) (-(s * t))) := by
              have h := Submodule.finrank_strictMono.monotone hincl2
              have h1 : Module.finrank K ↥(V2 ⊔ V3) = 2 := by
                have h := Submodule.finrank_sup_add_finrank_inf_eq V2 V3
                rw [hV23, finrank_bot, add_zero] at h
                omega
              rwa [h1] at h
            have hbal : Module.finrank K (Module.End.eigenspace (T.comp U) (-(s * t))) = 2 := by
              have hcompl := isCompl_eigenspace_of_sq h2 hst0 hE2c
              have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
              rw [Module.finrank_fin_fun] at hsum
              omega
            have hbal2 : Module.finrank K (Module.End.eigenspace (T.comp U) (s * t)) = 2 := by
              have hcompl := isCompl_eigenspace_of_sq h2 hst0 hE2c
              have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
              rw [Module.finrank_fin_fun] at hsum
              omega
            have hdAB : (Ma * Mb).det = (s * t) ^ 4 := by
              have hdet := det_eq_pow_mul_pow (T := T.comp U) h2 hst0 hE2c
              rw [hbal2, hbal] at hdet
              rw [← LinearMap.det_toLin', hlin, hdet]
              ring
            exact absurd ⟨exists_det_smul_eq_one_of_det_pow hNs hs0 hdA,
              exists_det_smul_eq_one_of_det_pow hNt ht0 hdB,
              exists_det_smul_eq_one_of_det_pow hNst hst0 hdAB⟩ hout
      ·
        obtain ⟨W, hW0, hti, hWU, hWT⟩ := stable_of_comm_anti h2 (by omega) hUiso ht0 hεt hU2 hcommE
        refine ⟨W, hW0, hti, ?_, hWU⟩
        intro w hw
        rw [← hTapp]
        exact hWT w hw
    ·
      obtain ⟨W, hW0, hti, hWT, hWU⟩ := stable_of_comm_anti h2 (by omega) hTiso hs0 hεs hT2
        fun v => (hcommE v).symm
      refine ⟨W, hW0, hti, hWT, ?_⟩
      intro w hw
      rw [← hUapp]
      exact hWU w hw
  ·
    have hantiE : ∀ v, T (U v) = -(U (T v)) := by
      intro v
      have h1 : Ma *ᵥ (Mb *ᵥ v) = -(Mb *ᵥ (Ma *ᵥ v)) := by
        have := congrArg (fun M => M *ᵥ v) hanti
        simpa [Matrix.neg_mulVec, Matrix.mulVec_mulVec] using this
      rw [hTapp, hUapp, hUapp, hTapp, h1]
    obtain ⟨W, hW0, hti, hWT, hWU⟩ := stable_of_anticomm hσ h2 hn hTiso hUiso hUinj hs0 hεs hT2
      (fun v => hU2 v) hantiE
    refine ⟨W, hW0, hti, ?_, ?_⟩
    · intro w hw
      rw [← hTapp]
      exact hWT w hw
    · intro w hw
      rw [← hUapp]
      exact hWU w hw

theorem exists_stable_isotropic_of_sq_scalar (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 3 ≤ n) (A B : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    {α β : K}
    (hA2 : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : GL (Fin n) K) = α • 1)
    (hB2 : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : GL (Fin n) K) = β • 1)
    (hAB : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : GL (Fin n) K) =
        (B : GL (Fin n) K) * (A : GL (Fin n) K) ∨
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : GL (Fin n) K) =
        -((B : GL (Fin n) K) * (A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hout : ¬ ((∃ c : K, h.norm c = 1 ∧
        (c • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1) ∧
      (∃ c : K, h.norm c = 1 ∧ (c • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1) ∧
      (∃ c : K, h.norm c = 1 ∧
        (c • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : GL (Fin n) K))).det = 1))) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y = 0) ∧
      (∀ w ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) ∧
      ∀ w ∈ W, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  obtain ⟨σ, hσ, hσbar⟩ := exists_unitaryInvolution h
  have h2 : (2 : K) ≠ 0 := by
    have := h.charP
    intro hzero
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp hzero
    have h1 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have h2' : 2 ≤ p := h.prime.two_le
    omega
  obtain ⟨W, hW0, hti, hWa, hWb⟩ := stable_isotropic_of_sq_scalar h hσ hσbar h2 hn
    (herm_toLin hσbar A.2) (herm_toLin hσbar B.2) hA2 hB2 hAB hout
  exact ⟨W, hW0, fun x hx y hy => by
    change gramForm h (1 : Matrix (Fin n) (Fin n) K) x y = 0
    rw [gramForm_one_eq_herm h hσbar]
    exact hti x hx y hy, hWa, hWb⟩

local notation "C₁" => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
local notation "C₁u" => (1 : GL (Fin n) K)

private lemma primeFormConjHom_mem_inner_of_smul_det_one
    (h : UnitaryFieldData p f K)
    {A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    {c : K} (hc : h.norm c = 1)
    (hdet : (c • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1) :
    primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : h.norm c = 0 := by
      rw [show h.norm c = c * h.bar c from rfl, h0, zero_mul]
    rw [h1] at hc
    exact zero_ne_one hc
  let cu : Kˣ := Units.mk0 c hc0
  have hcu : (cu : K) = c := rfl
  have hcu_norm : h.bar (cu : K) * (cu : K) = 1 := by
    rw [hcu, mul_comm]
    exact hc
  let g : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) cu * (A : GL (Fin n) K)
  have hg_eq : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [show g = GeneralLinearGroup.scalar (Fin n) cu * (A : GL (Fin n) K) from rfl]
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, hcu]
  have hz_unitary : (GeneralLinearGroup.scalar (Fin n) cu : GL (Fin n) K) ∈
      primeFormUnitary h C₁ := by
    rw [mem_primeFormUnitary]
    rw [GeneralLinearGroup.coe_one, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
    rw [Matrix.map_smul' h.bar (cu : K) (1 : Matrix (Fin n) (Fin n) K)
      (fun a b => map_mul h.bar a b)]
    rw [Matrix.map_one h.bar (map_zero h.bar) (map_one h.bar)]
    rw [Matrix.transpose_smul, Matrix.transpose_one]
    rw [Matrix.smul_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one]
    rw [smul_smul, mul_comm, hcu_norm, one_smul]
  have hA_unitary : (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have h := mem_primeFormUnitary.mp A.2
    simp only [GeneralLinearGroup.coe_one, mul_one] at h
    exact h
  have hg_unitary : g ∈ primeFormUnitary h C₁ := by
    rw [mem_primeFormUnitary]
    rw [GeneralLinearGroup.coe_one, hg_eq]
    rw [Matrix.map_smul' h.bar c ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (fun a b => map_mul h.bar a b)]
    rw [Matrix.transpose_smul]
    rw [Matrix.smul_mul, Matrix.mul_one]
    rw [Matrix.mul_smul]
    rw [Matrix.smul_mul]
    rw [smul_smul, mul_comm]
    rw [hA_unitary]
    rw [← hcu, hcu_norm, one_smul]
  have hg_det : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [hg_eq]
    exact hdet
  have hg_su : g ∈ gramSU h C₁ := by
    rw [mem_gramSU_iff_unitary]
    exact ⟨hg_unitary, hg_det⟩
  have hz_ker : primeFormConjHom h C₁
      ⟨GeneralLinearGroup.scalar (Fin n) cu, hz_unitary⟩ = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H s =>
      rw [primeFormConjHom_mk, MulAut.one_apply]
      congr 1
      refine Subtype.ext ?_
      change GeneralLinearGroup.scalar (Fin n) cu * (s : GL (Fin n) K) *
        (GeneralLinearGroup.scalar (Fin n) cu)⁻¹ = (s : GL (Fin n) K)
      rw [GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel, mul_one]
  have hg_decomp : (⟨g, hg_unitary⟩ : primeFormUnitary h C₁) =
      ⟨GeneralLinearGroup.scalar (Fin n) cu, hz_unitary⟩ * A := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
  have hconj : primeFormConjHom h C₁ ⟨g, hg_unitary⟩ = primeFormConjHom h C₁ A := by
    rw [hg_decomp, map_mul, hz_ker, one_mul]
  rw [mem_inner_primeFormP]
  exact ⟨⟨g, hg_su⟩, by simpa using hconj.symm⟩

private lemma sq_eq_one_of_mul_eq_smul_mul {A B : GL (Fin n) K} {α γ : K}
    (hn : 0 < n) (hα : α ≠ 0)
    (hA2 : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hAB : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      γ • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    γ * γ = 1 := by
  have hB_inv : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((B⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : α • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (γ * γ * α) • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    calc α • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hA2, Matrix.smul_mul, Matrix.one_mul]
      _ = ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [Matrix.mul_assoc]
      _ = ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (γ • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by rw [hAB]
      _ = γ • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
          rw [Matrix.mul_smul]
      _ = γ • ((((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [Matrix.mul_assoc]
      _ = γ • ((γ • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hAB]
      _ = γ • (γ • ((((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
          rw [Matrix.smul_mul]
      _ = (γ * γ) • ((((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [smul_smul]
      _ = (γ * γ) • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
          rw [Matrix.mul_assoc]
      _ = (γ * γ) • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (α • 1)) := by rw [hA2]
      _ = (γ * γ) • (α • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
      _ = (γ * γ * α) • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [smul_smul]
  have h2 : α • (1 : Matrix (Fin n) (Fin n) K) =
      (γ * γ * α) • (1 : Matrix (Fin n) (Fin n) K) := by
    calc α • (1 : Matrix (Fin n) (Fin n) K)
        = α • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (((B⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) := by rw [hB_inv]
      _ = (α • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            (((B⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
          rw [Matrix.smul_mul]
      _ = ((γ * γ * α) • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            (((B⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by rw [h1]
      _ = (γ * γ * α) • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (((B⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) := by
          rw [Matrix.smul_mul]
      _ = (γ * γ * α) • (1 : Matrix (Fin n) (Fin n) K) := by rw [hB_inv]
  have h3 : α = γ * γ * α := by
    have h4 := congrArg (fun M => M ⟨0, hn⟩ ⟨0, hn⟩) h2
    simpa [Matrix.smul_one_eq_diagonal] using h4
  have h4 : γ * γ * α = 1 * α := by
    rw [one_mul]
    exact h3.symm
  exact mul_right_cancel₀ hα h4

theorem exists_stable_isotropic_of_le_primeFormD (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 3 ≤ n)
    {E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hED : E ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hEI : ¬ E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y = 0) ∧
      ∀ e ∈ E, ∃ (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (φ : K ≃+* K),
        primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
          ⟨A, φ⟩ = e ∧
        ∀ w ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (w i)) ∈ W := by
  have hC₁ : IsPrimeFormGram C₁u :=
    CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
  classical
  have := @Fintype.ofFinite E
    (Nat.finite_of_card_ne_zero (α := E) (by rw [h4]; norm_num))
  have hcard : Fintype.card E = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact h4
  have ha : ∃ a : E, a ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset E) ⊆ ({1} : Finset E) := by
      intro x _
      rw [Finset.mem_singleton]
      exact h x
    have hcard_le : Fintype.card E ≤ 1 := by
      calc Fintype.card E = (Finset.univ : Finset E).card := by rw [Finset.card_univ]
        _ ≤ ({1} : Finset E).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton 1
    omega
  obtain ⟨a, ha1⟩ := ha
  have hb : ∃ b : E, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset E) ⊆ insert a ({1} : Finset E) := by
      intro x _
      rw [Finset.mem_insert]
      by_cases hx1 : x = 1
      · right
        rw [hx1]
        exact Finset.mem_singleton_self 1
      · left
        exact h x hx1
    have hcard_le : Fintype.card E ≤ 2 := by
      calc Fintype.card E = (Finset.univ : Finset E).card := by rw [Finset.card_univ]
        _ ≤ (insert a ({1} : Finset E)).card := Finset.card_le_card hsub
        _ = 2 := by
          rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_singleton]
          · rw [Finset.mem_singleton]
            exact ha1
    omega
  obtain ⟨b, hb1, hba⟩ := hb
  let a' : MulAut (primeFormP h C₁) := a.val
  let b' : MulAut (primeFormP h C₁) := b.val
  have ha1' : a' ≠ 1 := by
    intro h
    exact ha1 (Subtype.ext h)
  have hb1' : b' ≠ 1 := by
    intro h
    exact hb1 (Subtype.ext h)
  have hba' : b' ≠ a' := by
    intro h
    exact hba (Subtype.ext h)
  have haD : a' ∈ primeFormD h C₁ := hED (x := ↑a) a.2
  have hbD : b' ∈ primeFormD h C₁ := hED (x := ↑b) b.2
  obtain ⟨A, hA⟩ : ∃ A : primeFormUnitary h C₁, primeFormConjHom h C₁ A = a' := by
    rw [primeFormD] at haD
    exact MonoidHom.mem_range.mp haD
  obtain ⟨B, hB⟩ : ∃ B : primeFormUnitary h C₁, primeFormConjHom h C₁ B = b' := by
    rw [primeFormD] at hbD
    exact MonoidHom.mem_range.mp hbD
  have ha2 : a' * a' = 1 := by
    have h : (↑a : MulAut (primeFormP h C₁)) ^ 2 = 1 := hE.2 (↑a) a.2
    simpa [pow_two] using h
  have hb2 : b' * b' = 1 := by
    have h : (↑b : MulAut (primeFormP h C₁)) ^ 2 = 1 := hE.2 (↑b) b.2
    simpa [pow_two] using h
  have hAA : primeFormConjHom h C₁ (A * A) = 1 := by
    rw [map_mul, hA]
    exact ha2
  have hBB : primeFormConjHom h C₁ (B * B) = 1 := by
    rw [map_mul, hB]
    exact hb2
  obtain ⟨αu, hα_norm, hA2_gl⟩ := eq_scalar_of_primeFormConjHom_eq_one h hC₁ hn hAA
  obtain ⟨βu, hβ_norm, hB2_gl⟩ := eq_scalar_of_primeFormConjHom_eq_one h hC₁ hn hBB
  have hA2 : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (αu : K) • 1 := by
    have h1 : (((A * A : primeFormUnitary h C₁) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((GeneralLinearGroup.scalar (Fin n) αu :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hA2_gl]
    rw [Subgroup.coe_mul, Units.val_mul] at h1
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at h1
    exact h1
  have hB2 : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (βu : K) • 1 := by
    have h1 : (((B * B : primeFormUnitary h C₁) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((GeneralLinearGroup.scalar (Fin n) βu :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hB2_gl]
    rw [Subgroup.coe_mul, Units.val_mul] at h1
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at h1
    exact h1
  have hcomm_ab : a' * b' = b' * a' := by
    have h := isMulCommutative_iff.mp hE.1 a b
    simpa [Subgroup.coe_mul] using congrArg Subtype.val h
  have hcommAB : primeFormConjHom h C₁ (A * B * (B * A)⁻¹) = 1 := by
    simp only [map_mul, map_inv, hA, hB, hcomm_ab, mul_inv_cancel]
  obtain ⟨γu, hγ_norm, hAB_gl⟩ := eq_scalar_of_primeFormConjHom_eq_one h hC₁ hn hcommAB
  have hAB_gl' : (A : GL (Fin n) K) * (B : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) γu *
        ((B : GL (Fin n) K) * (A : GL (Fin n) K)) := by
    have h1 : (A * B * (B * A)⁻¹ : primeFormUnitary h C₁) * (B * A) = A * B := by
      group
    calc (A : GL (Fin n) K) * (B : GL (Fin n) K)
        = (((A * B : primeFormUnitary h C₁) : GL (Fin n) K)) := by rw [Subgroup.coe_mul]
      _ = ((((A * B * (B * A)⁻¹ : primeFormUnitary h C₁) * (B * A) :
            primeFormUnitary h C₁) : GL (Fin n) K)) := by rw [h1]
      _ = (((A * B * (B * A)⁻¹ : primeFormUnitary h C₁) : GL (Fin n) K)) *
            (((B * A : primeFormUnitary h C₁) : GL (Fin n) K)) := by rw [Subgroup.coe_mul]
      _ = GeneralLinearGroup.scalar (Fin n) γu *
            (((B * A : primeFormUnitary h C₁) : GL (Fin n) K)) := by rw [hAB_gl]
      _ = GeneralLinearGroup.scalar (Fin n) γu *
            ((B : GL (Fin n) K) * (A : GL (Fin n) K)) := by rw [Subgroup.coe_mul]
  have hAB : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (γu : K) • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    have h1 := congrArg (fun (x : GL (Fin n) K) => ((x : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) hAB_gl'
    simp only [Units.val_mul] at h1
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      Matrix.smul_mul, Matrix.one_mul] at h1
    exact h1
  have hα0 : (αu : K) ≠ 0 := by
    intro h0
    have h1 : h.norm (αu : K) = 0 := by
      rw [show h.norm (αu : K) = (αu : K) * h.bar (αu : K) from rfl, h0, zero_mul]
    rw [h1] at hα_norm
    exact zero_ne_one hα_norm
  have hγ2 : (γu : K) * (γu : K) = 1 :=
    sq_eq_one_of_mul_eq_smul_mul (n := n) (by omega) hα0 hA2 hAB
  have hγ : (γu : K) = 1 ∨ (γu : K) = -1 := by
    rw [← sq_eq_one_iff]
    rw [pow_two]
    exact hγ2
  have hAB_disj : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∨
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      -(((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rcases hγ with hγ1 | hγneg
    · left
      rw [hAB, hγ1, one_smul]
    · right
      rw [hAB, hγneg, neg_one_smul]
  have hab1 : a' * b' ≠ 1 := by
    intro h
    have h1 : a' = b' := by
      calc a' = a' * 1 := by rw [mul_one]
        _ = a' * (b' * b') := by rw [hb2]
        _ = (a' * b') * b' := by rw [mul_assoc]
        _ = 1 * b' := by rw [h]
        _ = b' := by rw [one_mul]
    exact hba' h1.symm
  have hab_a : a' * b' ≠ a' := by
    intro h
    exact hb1' (mul_left_cancel (by rw [h, mul_one]))
  have hab_b : a' * b' ≠ b' := by
    intro h
    exact ha1' (mul_right_cancel (by rw [h, one_mul]))
  let ab : E := a * b
  have hab_val : (ab : MulAut (primeFormP h C₁)) = a' * b' := by
    rw [show ab = a * b from rfl, Subgroup.coe_mul]
  have h1a : (1 : E) ≠ a := by
    intro h
    exact ha1 h.symm
  have h1b : (1 : E) ≠ b := by
    intro h
    exact hb1 h.symm
  have h1ab : (1 : E) ≠ ab := by
    intro h
    apply hab1
    have hc := congrArg Subtype.val h
    rw [Subgroup.coe_one, hab_val] at hc
    exact hc.symm
  have hab' : a ≠ b := by
    intro h
    exact hba (by simpa using (congrArg Subtype.val h).symm)
  have haab : a ≠ ab := by
    intro h
    apply hab_a
    have hc := congrArg Subtype.val h
    rw [hab_val] at hc
    exact hc.symm
  have hbab : b ≠ ab := by
    intro h
    apply hab_b
    have hc := congrArg Subtype.val h
    rw [hab_val] at hc
    exact hc.symm
  let s1 : Finset E := {ab}
  let s2 : Finset E := insert b s1
  let s3 : Finset E := insert a s2
  let s : Finset E := insert (1 : E) s3
  have hs1 : (1 : E) ∉ s3 := by
    simp only [s3, s2, s1, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1a, h1b, h1ab⟩
  have hs2 : a ∉ s2 := by
    simp only [s2, s1, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab', haab⟩
  have hs3 : b ∉ s1 := by
    simp only [s1, Finset.mem_singleton]
    exact hbab
  have hs : s.card = 4 := by
    have e1 : s.card = s3.card + 1 := Finset.card_insert_of_notMem hs1
    have e2 : s3.card = s2.card + 1 := Finset.card_insert_of_notMem hs2
    have e3 : s2.card = s1.card + 1 := Finset.card_insert_of_notMem hs3
    have e4 : s1.card = 1 := Finset.card_singleton _
    omega
  have huniv : s = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x _
      exact Finset.mem_univ x
    · rw [Finset.card_univ, hcard, hs]
  have hcover : ∀ e ∈ E, e = 1 ∨ e = a' ∨ e = b' ∨ e = a' * b' := by
    intro e he
    have hmem : (⟨e, he⟩ : E) ∈ s := by
      rw [huniv]
      exact Finset.mem_univ _
    simp only [s, s3, s2, s1, Finset.mem_insert, Finset.mem_singleton,
      Subtype.ext_iff] at hmem
    rcases hmem with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · right; right; right
      rw [hab_val] at h
      exact h
  have hout : ¬ ((∃ c : K, h.norm c = 1 ∧
      (c • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1) ∧
    (∃ c : K, h.norm c = 1 ∧
      (c • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1) ∧
    (∃ c : K, h.norm c = 1 ∧
      (c • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (B : GL (Fin n) K))).det = 1)) := by
    rintro ⟨⟨c₁, hc₁_norm, hc₁_det⟩, ⟨c₂, hc₂_norm, hc₂_det⟩, ⟨c₃, hc₃_norm, hc₃_det⟩⟩
    apply hEI
    intro e he
    rcases hcover e he with h1 | h1 | h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1, ← hA]
      exact primeFormConjHom_mem_inner_of_smul_det_one h hc₁_norm hc₁_det
    · rw [h1, ← hB]
      exact primeFormConjHom_mem_inner_of_smul_det_one h hc₂_norm hc₂_det
    · have hdet : (c₃ • (((A * B : primeFormUnitary h C₁) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)).det = 1 := by
        rw [Subgroup.coe_mul, Units.val_mul]
        exact hc₃_det
      rw [h1, ← hA, ← hB, ← map_mul]
      exact primeFormConjHom_mem_inner_of_smul_det_one h hc₃_norm hdet
  obtain ⟨W, hW0, hti, hWa, hWb⟩ :=
    exists_stable_isotropic_of_sq_scalar h hp hn A B hA2 hB2 hAB_disj hout
  refine ⟨W, hW0, hti, ?_⟩
  intro e he
  rcases hcover e he with h1 | h1 | h1 | h1
  · refine ⟨(1 : primeFormUnitary h C₁), (1 : K ≃+* K), ?_, ?_⟩
    · rw [h1, primeFormPsi_apply, map_one, map_one, mul_one]
    · intro w hw
      simpa using hw
  · refine ⟨A, (1 : K ≃+* K), ?_, ?_⟩
    · rw [h1, primeFormPsi_apply, map_one, mul_one, hA]
    · intro w hw
      simpa using hWa w hw
  · refine ⟨B, (1 : K ≃+* K), ?_, ?_⟩
    · rw [h1, primeFormPsi_apply, map_one, mul_one, hB]
    · intro w hw
      simpa using hWb w hw
  · refine ⟨A * B, (1 : K ≃+* K), ?_, ?_⟩
    · rw [h1, primeFormPsi_apply, map_one, mul_one, map_mul, hA, hB]
    · intro w hw
      change (((A * B : primeFormUnitary h C₁) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W
      rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hWa _ (hWb w hw)

end CFSG.LocalAnalysis.WeakClosure81.UOuter
