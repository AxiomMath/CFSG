module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofAutY
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
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
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj StatedScalars)

namespace Item812Res3

section SpReal

open Matrix
open CFSG.RankThree.SubgroupLists (spForm spForm_self spForm_isAlt spTrans spTrans_mulVec
  spTrans_mem_statedSp)

variable {F : Type} [Field F] [CharP F 2] {n : ℕ}

local notation "𝕍" => Fin n ⊕ Fin n → F
local notation "𝕄" => Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F
local notation "𝔹" => spForm n F

theorem spForm_comm_charTwo (u v : 𝕍) : 𝔹 u v = 𝔹 v u := by
  rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt u v, CharTwo.neg_eq]

omit [CharP F 2] in
theorem spForm_smul_mulVec_smul (M : 𝕄) (c : F) (u : 𝕍) :
    𝔹 (c • u) (M *ᵥ (c • u)) = c * c * 𝔹 u (M *ᵥ u) := by
  simp only [mulVec_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem spForm_polar {M : 𝕄} (hM : ∀ u v, 𝔹 (M *ᵥ u) (M *ᵥ v) = 𝔹 u v) {v₀ v₁ : 𝕍}
    (h₀ : M *ᵥ (M *ᵥ v₀) = M *ᵥ v₀ + v₀) :
    𝔹 (v₀ + v₁) (M *ᵥ (v₀ + v₁)) = 𝔹 v₀ (M *ᵥ v₀) + 𝔹 v₁ (M *ᵥ v₁) + 𝔹 v₀ v₁ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e1 : 𝔹 v₁ (M *ᵥ v₀) = 𝔹 v₁ v₀ + 𝔹 (M *ᵥ v₁) v₀ := by
    rw [← hM v₁ (M *ᵥ v₀), h₀, map_add, hM]
  have s1 := spForm_comm_charTwo v₀ (M *ᵥ v₁)
  have s2 := spForm_comm_charTwo v₀ v₁
  simp only [mulVec_add, map_add, LinearMap.add_apply]
  linear_combination e1 + s1 - s2 + 𝔹 (M *ᵥ v₁) v₀ * h2

theorem exists_mem_spForm_mulVec_eq_one [Finite F] {M : 𝕄}
    (hM : ∀ u v, 𝔹 (M *ᵥ u) (M *ᵥ v) = 𝔹 u v) {U : Submodule F 𝕍}
    (hUW : ∀ u ∈ U, M *ᵥ (M *ᵥ u) = M *ᵥ u + u)
    (hnd : ∀ u ∈ U, (∀ w ∈ U, 𝔹 w u = 0) → u = 0) (hU : U ≠ ⊥) :
    ∃ e ∈ U, 𝔹 e (M *ᵥ e) = 1 := by
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨w, hw, hwu⟩ : ∃ w ∈ U, 𝔹 w u₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hu₀0 (hnd u₀ hu₀ h)
  have hres : ∀ v ∈ U, 𝔹 v (M *ᵥ v) ≠ 0 → ∃ e ∈ U, 𝔹 e (M *ᵥ e) = 1 := by
    intro v hv hQ
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' (𝔹 v (M *ᵥ v))⁻¹
    refine ⟨r • v, U.smul_mem r hv, ?_⟩
    rw [spForm_smul_mulVec_smul, ← hr, inv_mul_cancel₀ hQ]
  by_cases h1 : 𝔹 w (M *ᵥ w) = 0
  · by_cases h2 : 𝔹 u₀ (M *ᵥ u₀) = 0
    · refine hres (w + u₀) (U.add_mem hw hu₀) ?_
      rw [spForm_polar hM (hUW w hw), h1, h2, zero_add, zero_add]
      exact hwu
    · exact hres u₀ hu₀ h2
  · exact hres w hw h1

theorem spForm_proj_eq_zero {M : 𝕄} {e : 𝕍} (he1 : 𝔹 e (M *ᵥ e) = 1) (u : 𝕍) :
    𝔹 e (u - (𝔹 (M *ᵥ e) u • e + 𝔹 e u • (M *ᵥ e))) = 0 ∧
      𝔹 (M *ᵥ e) (u - (𝔹 (M *ᵥ e) u • e + 𝔹 e u • (M *ᵥ e))) = 0 := by
  have hfe : 𝔹 (M *ᵥ e) e = 1 := by rw [spForm_comm_charTwo, he1]
  constructor
  · simp only [map_sub, map_add, map_smul, smul_eq_mul, spForm_self, he1]
    ring
  · simp only [map_sub, map_add, map_smul, smul_eq_mul, spForm_self, hfe]
    ring

omit [CharP F 2] in
theorem exists_inverting_bot {M : 𝕄} {U : Submodule F 𝕍} (hU : U = ⊥) :
    ∃ T : GL (Fin n ⊕ Fin n) F, T ∈ StatedSp n F ∧
      (∀ v, (∀ w ∈ U, 𝔹 w v = 0) → (T : 𝕄) *ᵥ v = v) ∧
      (∀ u ∈ U, (T : 𝕄) *ᵥ u ∈ U) ∧
      ∀ u ∈ U, (T : 𝕄) *ᵥ (M *ᵥ u) = M *ᵥ (M *ᵥ ((T : 𝕄) *ᵥ u)) := by
  subst hU
  refine ⟨1, one_mem _, fun v _ => by rw [Units.val_one, one_mulVec], fun u hu => ?_,
    fun u hu => ?_⟩
  · rw [Units.val_one, one_mulVec]
    exact hu
  · rw [Submodule.mem_bot] at hu
    subst hu
    simp only [mulVec_zero]

theorem exists_inverting_step {M : 𝕄} (hM : ∀ u v, 𝔹 (M *ᵥ u) (M *ᵥ v) = 𝔹 u v)
    (hM3 : ∀ v, M *ᵥ (M *ᵥ (M *ᵥ v)) = v) {U : Submodule F 𝕍}
    (hUM : ∀ u ∈ U, M *ᵥ u ∈ U) (hUW : ∀ u ∈ U, M *ᵥ (M *ᵥ u) = M *ᵥ u + u)
    {e : 𝕍} (he : e ∈ U) (he1 : 𝔹 e (M *ᵥ e) = 1) {T' : GL (Fin n ⊕ Fin n) F}
    (hT' : T' ∈ StatedSp n F)
    (h1 : ∀ v, (∀ w ∈ U, 𝔹 e w = 0 → 𝔹 (M *ᵥ e) w = 0 → 𝔹 w v = 0) → (T' : 𝕄) *ᵥ v = v)
    (h2 : ∀ u ∈ U, 𝔹 e u = 0 → 𝔹 (M *ᵥ e) u = 0 →
      (T' : 𝕄) *ᵥ u ∈ U ∧ 𝔹 e ((T' : 𝕄) *ᵥ u) = 0 ∧ 𝔹 (M *ᵥ e) ((T' : 𝕄) *ᵥ u) = 0)
    (h3 : ∀ u ∈ U, 𝔹 e u = 0 → 𝔹 (M *ᵥ e) u = 0 →
      (T' : 𝕄) *ᵥ (M *ᵥ u) = M *ᵥ (M *ᵥ ((T' : 𝕄) *ᵥ u))) :
    ∃ T : GL (Fin n ⊕ Fin n) F, T ∈ StatedSp n F ∧
      (∀ v, (∀ w ∈ U, 𝔹 w v = 0) → (T : 𝕄) *ᵥ v = v) ∧
      (∀ u ∈ U, (T : 𝕄) *ᵥ u ∈ U) ∧
      ∀ u ∈ U, (T : 𝕄) *ᵥ (M *ᵥ u) = M *ᵥ (M *ᵥ ((T : 𝕄) *ᵥ u)) := by
  have hfU : M *ᵥ e ∈ U := hUM e he
  have hee : 𝔹 e e = 0 := spForm_self e
  have hff : 𝔹 (M *ᵥ e) (M *ᵥ e) = 0 := spForm_self _
  have hfe : 𝔹 (M *ᵥ e) e = 1 := by rw [spForm_comm_charTwo, he1]
  have haU : e + M *ᵥ e ∈ U := U.add_mem he hfU
  have hvv : ∀ v : 𝕍, v + v = 0 := fun v => by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  set τ := spTrans (e + M *ᵥ e) (1 : F) with hτ
  have hτfix : ∀ v, 𝔹 v (e + M *ᵥ e) = 0 → (τ : 𝕄) *ᵥ v = v := fun v hv => by
    rw [hτ, spTrans_mulVec, hv, mul_zero, zero_smul, add_zero]
  have hτe : (τ : 𝕄) *ᵥ e = M *ᵥ e := by
    rw [hτ, spTrans_mulVec, map_add, hee, he1, zero_add, one_mul, one_smul, ← add_assoc, hvv,
      zero_add]
  have hτf : (τ : 𝕄) *ᵥ (M *ᵥ e) = e := by
    rw [hτ, spTrans_mulVec, map_add, hfe, hff, add_zero, one_mul, one_smul, add_comm e (M *ᵥ e),
      ← add_assoc, hvv, zero_add]
  have hperp : ∀ w, 𝔹 e w = 0 → 𝔹 (M *ᵥ e) w = 0 → 𝔹 w (e + M *ᵥ e) = 0 := fun w hw1 hw2 => by
    rw [map_add, spForm_comm_charTwo w e, spForm_comm_charTwo w (M *ᵥ e), hw1, hw2, add_zero]
  have hP'M : ∀ w ∈ U, 𝔹 e w = 0 → 𝔹 (M *ᵥ e) w = 0 →
      M *ᵥ w ∈ U ∧ 𝔹 e (M *ᵥ w) = 0 ∧ 𝔹 (M *ᵥ e) (M *ᵥ w) = 0 := fun w hw hw1 hw2 => by
    refine ⟨hUM w hw, ?_, by rw [hM, hw1]⟩
    rw [← hM e (M *ᵥ w), hUW w hw, map_add, hM, hw1, hw2, add_zero]
  have hT'e : (T' : 𝕄) *ᵥ e = e := h1 e fun w _ hw1 _ => by rw [spForm_comm_charTwo, hw1]
  have hT'f : (T' : 𝕄) *ᵥ (M *ᵥ e) = M *ᵥ e :=
    h1 (M *ᵥ e) fun w _ _ hw2 => by rw [spForm_comm_charTwo, hw2]
  have hT'U : ∀ u ∈ U, (T' : 𝕄) *ᵥ u ∈ U := by
    intro u hu
    obtain ⟨hp1, hp2⟩ := spForm_proj_eq_zero he1 u
    have hu' : u - (𝔹 (M *ᵥ e) u • e + 𝔹 e u • (M *ᵥ e)) ∈ U :=
      U.sub_mem hu (U.add_mem (U.smul_mem _ he) (U.smul_mem _ hfU))
    have hdec : (T' : 𝕄) *ᵥ u = (T' : 𝕄) *ᵥ (u - (𝔹 (M *ᵥ e) u • e + 𝔹 e u • (M *ᵥ e))) +
        (𝔹 (M *ᵥ e) u • e + 𝔹 e u • (M *ᵥ e)) := by
      conv_lhs => rw [← sub_add_cancel u (𝔹 (M *ᵥ e) u • e + 𝔹 e u • (M *ᵥ e))]
      rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hT'e, hT'f]
    rw [hdec]
    exact U.add_mem (h2 _ hu' hp1 hp2).1 (U.add_mem (U.smul_mem _ he) (U.smul_mem _ hfU))
  refine ⟨τ * T', mul_mem (spTrans_mem_statedSp _ _) hT', ?_, ?_, ?_⟩
  · intro v hv
    rw [Units.val_mul, ← mulVec_mulVec, h1 v fun w hw _ _ => hv w hw]
    apply hτfix
    rw [map_add, spForm_comm_charTwo v e, spForm_comm_charTwo v (M *ᵥ e), hv e he, hv _ hfU,
      add_zero]
  · intro u hu
    rw [Units.val_mul, ← mulVec_mulVec, hτ, spTrans_mulVec]
    exact U.add_mem (hT'U u hu) (U.smul_mem _ haU)
  · intro u hu
    simp only [Units.val_mul, ← mulVec_mulVec]
    obtain ⟨hp1, hp2⟩ := spForm_proj_eq_zero he1 u
    have hu' : u - (𝔹 (M *ᵥ e) u • e + 𝔹 e u • (M *ᵥ e)) ∈ U :=
      U.sub_mem hu (U.add_mem (U.smul_mem _ he) (U.smul_mem _ hfU))
    set u' := u - (𝔹 (M *ᵥ e) u • e + 𝔹 e u • (M *ᵥ e)) with hu'def
    set α := 𝔹 (M *ᵥ e) u
    set β := 𝔹 e u
    have huu : u = u' + (α • e + β • (M *ᵥ e)) := (sub_add_cancel u _).symm
    have hA : (τ : 𝕄) *ᵥ ((T' : 𝕄) *ᵥ (M *ᵥ u')) = M *ᵥ (M *ᵥ ((τ : 𝕄) *ᵥ ((T' : 𝕄) *ᵥ u'))) := by
      obtain ⟨hw, hw1, hw2⟩ := h2 u' hu' hp1 hp2
      obtain ⟨hMw, hMw1, hMw2⟩ := hP'M _ hw hw1 hw2
      obtain ⟨-, hMMw1, hMMw2⟩ := hP'M _ hMw hMw1 hMw2
      rw [h3 u' hu' hp1 hp2, hτfix _ (hperp _ hMMw1 hMMw2), hτfix _ (hperp _ hw1 hw2)]
    have hB : (τ : 𝕄) *ᵥ ((T' : 𝕄) *ᵥ (M *ᵥ e)) = M *ᵥ (M *ᵥ ((τ : 𝕄) *ᵥ ((T' : 𝕄) *ᵥ e))) := by
      rw [hT'f, hτf, hT'e, hτe, hM3]
    have hC : (τ : 𝕄) *ᵥ ((T' : 𝕄) *ᵥ (M *ᵥ (M *ᵥ e))) =
        M *ᵥ (M *ᵥ ((τ : 𝕄) *ᵥ ((T' : 𝕄) *ᵥ (M *ᵥ e)))) := by
      rw [hUW e he, mulVec_add, hT'f, hT'e, mulVec_add, hτf, hτe, hUW e he, add_comm]
    conv_lhs => rw [huu]
    conv_rhs => rw [huu]
    simp only [mulVec_add, mulVec_smul]
    rw [hA, hC, hB]

theorem exists_inverting_on [Finite F] {M : 𝕄}
    (hM : ∀ u v, 𝔹 (M *ᵥ u) (M *ᵥ v) = 𝔹 u v) (hM3 : ∀ v, M *ᵥ (M *ᵥ (M *ᵥ v)) = v)
    (k : ℕ) : ∀ U : Submodule F 𝕍, Module.finrank F U ≤ k →
      (∀ u ∈ U, M *ᵥ u ∈ U) → (∀ u ∈ U, M *ᵥ (M *ᵥ u) = M *ᵥ u + u) →
      (∀ u ∈ U, (∀ w ∈ U, 𝔹 w u = 0) → u = 0) →
      ∃ T : GL (Fin n ⊕ Fin n) F, T ∈ StatedSp n F ∧
        (∀ v, (∀ w ∈ U, 𝔹 w v = 0) → (T : 𝕄) *ᵥ v = v) ∧
        (∀ u ∈ U, (T : 𝕄) *ᵥ u ∈ U) ∧
        ∀ u ∈ U, (T : 𝕄) *ᵥ (M *ᵥ u) = M *ᵥ (M *ᵥ ((T : 𝕄) *ᵥ u)) := by
  induction k with
  | zero =>
    intro U hk _ _ _
    exact exists_inverting_bot (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hk))
  | succ k ih =>
    intro U hk hUM hUW hnd
    by_cases hU : U = ⊥
    · exact exists_inverting_bot hU
    obtain ⟨e, he, he1⟩ := exists_mem_spForm_mulVec_eq_one hM hUW hnd hU
    have hfe : 𝔹 (M *ᵥ e) e = 1 := by rw [spForm_comm_charTwo, he1]
    set U' : Submodule F 𝕍 := U ⊓ LinearMap.ker (𝔹 e) ⊓ LinearMap.ker (𝔹 (M *ᵥ e)) with hU'
    have hmem : ∀ w, w ∈ U' ↔ w ∈ U ∧ 𝔹 e w = 0 ∧ 𝔹 (M *ᵥ e) w = 0 := fun w => by
      rw [hU', Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker,
        and_assoc]
    have hU'M : ∀ w ∈ U', M *ᵥ w ∈ U' := by
      intro w hw
      obtain ⟨hw, hw1, hw2⟩ := (hmem w).mp hw
      refine (hmem _).mpr ⟨hUM w hw, ?_, by rw [hM, hw1]⟩
      rw [← hM e (M *ᵥ w), hUW w hw, map_add, hM, hw1, hw2, add_zero]
    have hlt : U' < U := by
      refine lt_of_le_of_ne (fun w hw => ((hmem w).mp hw).1) fun h => ?_
      have h' : e ∈ U' := h ▸ he
      rw [((hmem e).mp h').2.2] at hfe
      exact zero_ne_one hfe
    have hk' : Module.finrank F U' ≤ k := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have hnd' : ∀ u ∈ U', (∀ w ∈ U', 𝔹 w u = 0) → u = 0 := by
      intro u hu hperp
      obtain ⟨hu, hu1, hu2⟩ := (hmem u).mp hu
      refine hnd u hu fun w hw => ?_
      obtain ⟨hp1, hp2⟩ := spForm_proj_eq_zero he1 w
      have hw' := hperp _ ((hmem _).mpr
        ⟨U.sub_mem hw (U.add_mem (U.smul_mem _ he) (U.smul_mem _ (hUM e he))), hp1, hp2⟩)
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, hu1, hu2, mul_zero, add_zero, sub_zero] at hw'
      exact hw'
    obtain ⟨T', hT', h1, h2, h3⟩ := ih U' hk' hU'M
      (fun u hu => hUW u ((hmem u).mp hu).1) hnd'
    exact exists_inverting_step hM hM3 hUM hUW he he1 hT'
      (fun v hv => h1 v fun w hw => by
        obtain ⟨hw, hw1, hw2⟩ := (hmem w).mp hw
        exact hv w hw hw1 hw2)
      (fun u hu hu1 hu2 => (hmem _).mp (h2 u ((hmem u).mpr ⟨hu, hu1, hu2⟩)))
      (fun u hu hu1 hu2 => h3 u ((hmem u).mpr ⟨hu, hu1, hu2⟩))

theorem exists_statedSp_conj_eq_inv [Finite F] {X : GL (Fin n ⊕ Fin n) F}
    (hX : X ∈ StatedSp n F) (hX3 : X ^ 3 = 1) : ∃ T ∈ StatedSp n F, T * X * T⁻¹ = X⁻¹ := by
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hM : ∀ u v, 𝔹 ((X : 𝕄) *ᵥ u) ((X : 𝕄) *ᵥ v) = 𝔹 u v :=
    SubgroupLists.spForm_mulVec hX
  have hM3 : ∀ v, (X : 𝕄) *ᵥ ((X : 𝕄) *ᵥ ((X : 𝕄) *ᵥ v)) = v := fun v => by
    have h := congrArg (fun g : GL (Fin n ⊕ Fin n) F => (g : 𝕄) *ᵥ v) hX3
    simp only [pow_succ, pow_zero, one_mul, Units.val_mul, Units.val_one, one_mulVec,
      ← mulVec_mulVec] at h
    exact h
  set M : 𝕄 := (X : 𝕄) with hMdef
  set W : Submodule F 𝕍 := LinearMap.ker (Matrix.toLin' (M * M + M + 1)) with hW
  have hmemW : ∀ v, v ∈ W ↔ M *ᵥ (M *ᵥ v) + M *ᵥ v + v = 0 := fun v => by
    rw [hW, LinearMap.mem_ker, Matrix.toLin'_apply, add_mulVec, add_mulVec, one_mulVec,
      ← mulVec_mulVec]
  have hWW : ∀ u ∈ W, M *ᵥ (M *ᵥ u) = M *ᵥ u + u := fun u hu => by
    have h := (hmemW u).mp hu
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at hi ⊢
    linear_combination hi - ((M *ᵥ u) i + u i) * h2F
  have hWM : ∀ u ∈ W, M *ᵥ u ∈ W := fun u hu => by
    have h := (hmemW u).mp hu
    rw [hmemW, hM3]
    calc u + M *ᵥ (M *ᵥ u) + M *ᵥ u = M *ᵥ (M *ᵥ u) + M *ᵥ u + u := by abel
      _ = 0 := h
  have hfixperp : ∀ u ∈ W, ∀ c : 𝕍, M *ᵥ c = c → 𝔹 u c = 0 := by
    intro u hu c hc
    have e2 : 𝔹 (M *ᵥ u) c = 𝔹 (M *ᵥ (M *ᵥ u)) c := by
      conv_rhs => rw [← hc]
      exact (hM _ _).symm
    have e3 : 𝔹 (M *ᵥ (M *ᵥ u)) c = 𝔹 (M *ᵥ u) c + 𝔹 u c := by
      rw [hWW u hu, map_add, LinearMap.add_apply]
    linear_combination -e2 - e3
  have hdec : ∀ y : 𝕍, y = (M *ᵥ (M *ᵥ y) + M *ᵥ y + y) + (M *ᵥ (M *ᵥ y) + M *ᵥ y) := by
    intro y
    funext i
    simp only [Pi.add_apply]
    linear_combination -((M *ᵥ (M *ᵥ y)) i + (M *ᵥ y) i) * h2F
  have hfix : ∀ y : 𝕍, M *ᵥ (M *ᵥ (M *ᵥ y) + M *ᵥ y + y) = M *ᵥ (M *ᵥ y) + M *ᵥ y + y := by
    intro y
    rw [mulVec_add, mulVec_add, hM3]
    abel
  have hwW : ∀ y : 𝕍, M *ᵥ (M *ᵥ y) + M *ᵥ y ∈ W := by
    intro y
    rw [hmemW]
    funext i
    simp only [mulVec_add, hM3, Pi.add_apply, Pi.zero_apply]
    linear_combination ((M *ᵥ y) i + y i + (M *ᵥ (M *ᵥ y)) i) * h2F
  have hWnd : ∀ u ∈ W, (∀ w ∈ W, 𝔹 w u = 0) → u = 0 := by
    intro u hu hperp
    refine SubgroupLists.spForm_separatingLeft u fun y => ?_
    rw [hdec y, map_add, hfixperp u hu _ (hfix y), zero_add, spForm_comm_charTwo]
    exact hperp _ (hwW y)
  obtain ⟨T, hT, h1, -, h3⟩ := exists_inverting_on hM hM3 _ W le_rfl hWM hWW hWnd
  refine ⟨T, hT, ?_⟩
  have hall : ∀ y : 𝕍, (T : 𝕄) *ᵥ (M *ᵥ y) = M *ᵥ (M *ᵥ ((T : 𝕄) *ᵥ y)) := by
    intro y
    have hc_fix := hfix y
    have hw := hwW y
    have hy := hdec y
    generalize M *ᵥ (M *ᵥ y) + M *ᵥ y + y = c at hc_fix hy
    generalize M *ᵥ (M *ᵥ y) + M *ᵥ y = w at hw hy
    have hc : (T : 𝕄) *ᵥ c = c := h1 _ fun w' hw' => hfixperp w' hw' _ hc_fix
    calc (T : 𝕄) *ᵥ (M *ᵥ y) = (T : 𝕄) *ᵥ (M *ᵥ (c + w)) := by rw [← hy]
      _ = c + M *ᵥ (M *ᵥ ((T : 𝕄) *ᵥ w)) := by
        rw [mulVec_add, hc_fix, mulVec_add, hc, h3 w hw]
      _ = M *ᵥ (M *ᵥ ((T : 𝕄) *ᵥ (c + w))) := by
        rw [mulVec_add, hc, mulVec_add, mulVec_add, hc_fix, hc_fix]
      _ = M *ᵥ (M *ᵥ ((T : 𝕄) *ᵥ y)) := by rw [← hy]
  have hXinv : X⁻¹ = X * X := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_three', hX3]
  have hTX : T * X = X⁻¹ * T := by
    refine SubgroupLists.gl_ext_mulVec fun y => ?_
    rw [hXinv, Units.val_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec,
      ← mulVec_mulVec, ← hMdef, hall]
  rw [hTX, mul_inv_cancel_right]

end SpReal

theorem real_of_mulEquiv {M N : Type*} [Group M] [Group N] (e : M ≃* N)
    (hN : ∀ x : N, x ^ 3 = 1 → ∃ y : N, y * x * y⁻¹ = x⁻¹) :
    ∀ x : M, x ^ 3 = 1 → ∃ y : M, y * x * y⁻¹ = x⁻¹ := by
  intro x hx
  obtain ⟨y, hy⟩ := hN (e x) (by rw [← map_pow, hx, map_one])
  refine ⟨e.symm y, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, hy]

end Item812Res3

section Final

open Item812Res3 in
theorem kFSp62Real : KFSp62Real := by
  refine real_of_mulEquiv (Sec4.projSpEquivStatedProj 3 (GaloisField 2 1)) ?_
  intro x hx
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num), pow_one]
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  have hA3 : (A : GL (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) ^ 3 = 1 := by
    have h1 : ((A ^ 3 : StatedSp 3 (GaloisField 2 1)) : StatedProj (StatedSp 3 (GaloisField 2 1)))
        = 1 := by
      rw [QuotientGroup.mk_pow, hx]
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    obtain ⟨u, hu⟩ := h2
    have hu1 : u = 1 := by
      apply Units.ext
      have h3 := FiniteField.pow_card_sub_one_eq_one (u : GaloisField 2 1) u.ne_zero
      rwa [hcard, pow_one] at h3
    rw [← Subgroup.coe_pow, ← hu, hu1, map_one]
  obtain ⟨T, hT, hTA⟩ := exists_statedSp_conj_eq_inv A.2 hA3
  refine ⟨((⟨T, hT⟩ : StatedSp 3 (GaloisField 2 1)) : StatedProj (StatedSp 3 (GaloisField 2 1))),
    ?_⟩
  have hsub : (⟨T, hT⟩ : StatedSp 3 (GaloisField 2 1)) * A *
      (⟨T, hT⟩ : StatedSp 3 (GaloisField 2 1))⁻¹ = A⁻¹ := Subtype.ext hTA
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, hsub,
    QuotientGroup.mk_inv]

theorem fin812Frattini : Fin812Frattini :=
  fin812Frattini_of_real kFSp62Real

end Final

end CFSG.RankThree.PartTwo.Sec8
