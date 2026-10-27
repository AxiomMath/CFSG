module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitStmt
public import CFSG.ClassicalGroups.Orthogonal.OddOrder
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec45
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjCited
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

local notation "M8" => Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K
local notation "GL8" => GL (Fin 4 ⊕ Fin 4) K

theorem statedQuadPlus_polar (x y : Fin 4 ⊕ Fin 4 → K) :
    StatedQuadPlus 4 K (x + y) - StatedQuadPlus 4 K x - StatedQuadPlus 4 K y =
      polar (quadPlus 4 K) x y := by
  rw [← coe_quadPlus]
  rfl

theorem isometry_of_mem_statedOmega {g : GL (Fin 4 ⊕ Fin 4) K}
    (hg : g ∈ StatedOmega (StatedQuadPlus 4 K)) (v : Fin 4 ⊕ Fin 4 → K) :
    quadPlus 4 K ((g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v) = quadPlus 4 K v := by
  rw [statedOmega_eq_comap (coe_quadPlus 4 K), Subgroup.mem_comap] at hg
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hle hg) v
  rwa [MulEquiv.coe_toMonoidHom, toLinEquiv_apply] at this

theorem polar_mulVec_of_isometry {g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K}
    (hg : ∀ v, quadPlus 4 K (g *ᵥ v) = quadPlus 4 K v) (x y : Fin 4 ⊕ Fin 4 → K) :
    polar (quadPlus 4 K) (g *ᵥ x) (g *ᵥ y) = polar (quadPlus 4 K) x y := by
  simp only [polar, ← Matrix.mulVec_add, hg]

variable {u w : Fin 4 ⊕ Fin 4 → K}

theorem polar_u_w (huw : IsTSLine8 u w) : polar (quadPlus 4 K) u w = 0 := by
  rw [← statedQuadPlus_polar, huw.2.1, huw.2.2.1, huw.2.2.2, sub_zero, sub_zero]

theorem quadPlus_u (huw : IsTSLine8 u w) : quadPlus 4 K u = 0 := by
  rw [coe_quadPlus]; exact huw.2.1

theorem quadPlus_w (huw : IsTSLine8 u w) : quadPlus 4 K w = 0 := by
  rw [coe_quadPlus]; exact huw.2.2.1

theorem quadPlus_mem_span (huw : IsTSLine8 u w) {x : Fin 4 ⊕ Fin 4 → K}
    (hx : x ∈ Submodule.span K {u, w}) : quadPlus 4 K x = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [QuadraticMap.map_add (quadPlus 4 K), QuadraticMap.map_smul, QuadraticMap.map_smul, quadPlus_u huw,
    quadPlus_w huw, polar_smul_left, polar_smul_right, polar_u_w huw]
  simp

theorem exists_dual_pair (huw : IsTSLine8 u w) :
    ∃ x₁ x₂ : Fin 4 ⊕ Fin 4 → K, polar (quadPlus 4 K) u x₁ = 1 ∧ polar (quadPlus 4 K) w x₁ = 0 ∧
      polar (quadPlus 4 K) u x₂ = 0 ∧ polar (quadPlus 4 K) w x₂ = 1 := by
  obtain ⟨g, hg⟩ := exists_dual_family (nondegenerate_polarBilin_quadPlus (n := 4) (K := K))
    huw.1
  refine ⟨g 0, g 1, ?_, ?_, ?_, ?_⟩
  · simpa using hg 0 0
  · simpa using hg 1 0
  · simpa using hg 0 1
  · simpa using hg 1 1

theorem longRoot8_shape (huw : IsTSLine8 u w) {g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K}
    (hg : ∀ v, quadPlus 4 K (g *ᵥ v) = quadPlus 4 K v)
    (h1 : ∀ v, g *ᵥ v - v ∈ Submodule.span K {u, w})
    (h2 : ∀ v, polar (quadPlus 4 K) v u = 0 → polar (quadPlus 4 K) v w = 0 → g *ᵥ v = v) :
    ∃ α β : K, ∀ v, g *ᵥ v - v =
      β • polar (quadPlus 4 K) v u • w + α • polar (quadPlus 4 K) v w • u := by
  obtain ⟨x₁, x₂, h11, h21, h12, h22⟩ := exists_dual_pair huw
  have hBD : ∀ v, polar (quadPlus 4 K) v (g *ᵥ v - v) = 0 := by
    intro v
    have hv := hg v
    have e : g *ᵥ v = v + (g *ᵥ v - v) := by abel
    rw [e, QuadraticMap.map_add (quadPlus 4 K), quadPlus_mem_span huw (h1 v)] at hv
    linear_combination hv
  obtain ⟨a₁, b₁, ha₁⟩ := Submodule.mem_span_pair.mp (h1 x₁)
  obtain ⟨a₂, b₂, ha₂⟩ := Submodule.mem_span_pair.mp (h1 x₂)
  have hB1 := hBD x₁
  rw [← ha₁, polar_add_right, polar_smul_right, polar_smul_right, polar_comm _ x₁ u,
    polar_comm _ x₁ w, h11, h21] at hB1
  have hB2 := hBD x₂
  rw [← ha₂, polar_add_right, polar_smul_right, polar_smul_right, polar_comm _ x₂ u,
    polar_comm _ x₂ w, h12, h22] at hB2
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at hB1 hB2
  refine ⟨a₂, b₁, fun v => ?_⟩
  set v' := v - polar (quadPlus 4 K) v u • x₁ - polar (quadPlus 4 K) v w • x₂ with hv'
  have hv'u : polar (quadPlus 4 K) v' u = 0 := by
    rw [hv', polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, polar_comm _ x₁ u,
      polar_comm _ x₂ u, h11, h12]
    ring
  have hv'w : polar (quadPlus 4 K) v' w = 0 := by
    rw [hv', polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, polar_comm _ x₁ w,
      polar_comm _ x₂ w, h21, h22]
    ring
  have hgv' := h2 v' hv'u hv'w
  have hdec : v = v' + polar (quadPlus 4 K) v u • x₁ + polar (quadPlus 4 K) v w • x₂ := by
    rw [hv']; abel
  have hlin : g *ᵥ v - v = polar (quadPlus 4 K) v u • (g *ᵥ x₁ - x₁) +
      polar (quadPlus 4 K) v w • (g *ᵥ x₂ - x₂) := by
    conv_lhs => rw [hdec]
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hgv']
    simp only [smul_sub]
    abel
  rw [hlin, ← ha₁, ← ha₂, hB1, hB2]
  simp only [zero_smul, zero_add, add_zero, smul_smul]
  rw [mul_comm (polar (quadPlus 4 K) v u), mul_comm (polar (quadPlus 4 K) v w)]

theorem conj_longRoot8 (huw : IsTSLine8 u w) {g A : GL (Fin 4 ⊕ Fin 4) K}
    (hg : ∀ v, quadPlus 4 K ((g : M8) *ᵥ v) = quadPlus 4 K v)
    (hgr : IsLongRoot8 u w g)
    (hA : ∀ v, quadPlus 4 K ((A : M8) *ᵥ v) = quadPlus 4 K v) {c : K}
    (hAu : (A : M8) *ᵥ u = c • u) (hAw : (A : M8) *ᵥ w = w) :
    ((A * g * A⁻¹ : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) - 1 =
        c • ((g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) - 1) ∧
      IsLongRoot8 u w (A * g * A⁻¹) := by
  have h2 : ∀ v, polar (quadPlus 4 K) v u = 0 → polar (quadPlus 4 K) v w = 0 →
      (g : M8) *ᵥ v = v := fun v hu hw =>
    hgr.2 v (by rw [statedQuadPlus_polar]; exact hu) (by rw [statedQuadPlus_polar]; exact hw)
  obtain ⟨α, β, hαβ⟩ := longRoot8_shape huw hg hgr.1 h2
  have hAinv : ∀ v, (A : M8) *ᵥ (((A⁻¹ : GL8) : M8) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have hBu : ∀ v, polar (quadPlus 4 K) (((A⁻¹ : GL8) : M8) *ᵥ v) u =
      c * polar (quadPlus 4 K) v u := fun v => by
    rw [← polar_mulVec_of_isometry hA, hAinv, hAu, polar_smul_right, smul_eq_mul]
  have hBw : ∀ v, polar (quadPlus 4 K) (((A⁻¹ : GL8) : M8) *ᵥ v) w =
      polar (quadPlus 4 K) v w := fun v => by
    rw [← polar_mulVec_of_isometry hA, hAinv, hAw]
  have key : ∀ v, ((A * g * A⁻¹ : GL8) : M8) *ᵥ v - v =
      c • ((g : M8) *ᵥ v - v) := by
    intro v
    have e1 : ((A * g * A⁻¹ : GL8) : M8) *ᵥ v =
        (A : M8) *ᵥ ((g : M8) *ᵥ (((A⁻¹ : GL8) : M8) *ᵥ v)) := by
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have e2 : (g : M8) *ᵥ (((A⁻¹ : GL8) : M8) *ᵥ v) =
        ((A⁻¹ : GL8) : M8) *ᵥ v +
          (β • polar (quadPlus 4 K) (((A⁻¹ : GL8) : M8) *ᵥ v) u • w +
            α • polar (quadPlus 4 K) (((A⁻¹ : GL8) : M8) *ᵥ v) w • u) := by
      rw [← hαβ]; abel
    rw [e1, e2, Matrix.mulVec_add, hAinv, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, hAu, hAw, hBu, hBw, hαβ]
    simp only [smul_smul, smul_add]
    rw [add_sub_cancel_left]
    congr 1 <;> congr 1 <;> ring
  refine ⟨Matrix.ext_of_mulVec_single fun j => ?_, fun v => ?_, fun v hu hw => ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, key, Matrix.smul_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec]
  · rw [key]
    exact Submodule.smul_mem _ c (hgr.1 v)
  · have := key v
    rw [h2 v (by rw [← statedQuadPlus_polar]; exact hu) (by rw [← statedQuadPlus_polar]; exact hw),
      sub_self, smul_zero, sub_eq_zero] at this
    exact this

section Torus

@[expose] noncomputable def torusLin (f u : Fin 4 ⊕ Fin 4 → K) (c : Kˣ) :
    (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K) where
  toFun v := v + ((c : K) - 1) • polar (quadPlus 4 K) v f • u +
    (((c⁻¹ : Kˣ) : K) - 1) • polar (quadPlus 4 K) v u • f
  map_add' v v' := by
    simp only [polar_add_left, add_smul, smul_add]
    abel
  map_smul' a v := by
    simp only [polar_smul_left, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]
    rw [smul_comm a ((c : K) - 1), smul_comm a (((c⁻¹ : Kˣ) : K) - 1)]

variable {f : Fin 4 ⊕ Fin 4 → K}

theorem torusLin_apply (c : Kˣ) (v : Fin 4 ⊕ Fin 4 → K) :
    torusLin f u c v = v + ((c : K) - 1) • polar (quadPlus 4 K) v f • u +
      (((c⁻¹ : Kˣ) : K) - 1) • polar (quadPlus 4 K) v u • f := rfl

variable (hu : quadPlus 4 K u = 0) (hf : quadPlus 4 K f = 0) (huf : polar (quadPlus 4 K) u f = 1)
include hu hf huf

theorem polar_torusLin_f (c : Kˣ) (v : Fin 4 ⊕ Fin 4 → K) :
    polar (quadPlus 4 K) (torusLin f u c v) f = (c : K) * polar (quadPlus 4 K) v f := by
  rw [torusLin_apply, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
    polar_smul_left, polar_smul_left, huf, polar_self, hf]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, mul_zero, add_zero, mul_one]
  ring

theorem polar_torusLin_u (c : Kˣ) (v : Fin 4 ⊕ Fin 4 → K) :
    polar (quadPlus 4 K) (torusLin f u c v) u = ((c⁻¹ : Kˣ) : K) * polar (quadPlus 4 K) v u := by
  rw [torusLin_apply, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
    polar_smul_left, polar_smul_left, polar_self, hu, polar_comm _ f u, huf]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, mul_zero, add_zero, mul_one, zero_add]
  ring

theorem torusLin_mul (c d : Kˣ) : torusLin f u (c * d) = (torusLin f u c).comp (torusLin f u d) := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, torusLin_apply c, polar_torusLin_f hu hf huf, polar_torusLin_u hu hf huf,
    torusLin_apply, torusLin_apply]
  simp only [Units.val_mul, mul_inv_rev, smul_smul]
  module

theorem torusLin_one : torusLin f u 1 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  simp [torusLin_apply]

@[expose] noncomputable def torusHom : Kˣ →* ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) where
  toFun c := LinearEquiv.ofLinear (torusLin f u c) (torusLin f u c⁻¹)
    (by rw [← torusLin_mul hu hf huf, mul_inv_cancel, torusLin_one hu hf huf])
    (by rw [← torusLin_mul hu hf huf, inv_mul_cancel, torusLin_one hu hf huf])
  map_one' := LinearEquiv.ext fun v => by
    show torusLin f u 1 v = v
    rw [torusLin_one hu hf huf, LinearMap.id_apply]
  map_mul' c d := LinearEquiv.ext fun v => by
    show torusLin f u (c * d) v = torusLin f u c (torusLin f u d v)
    rw [torusLin_mul hu hf huf, LinearMap.comp_apply]

theorem torusHom_apply (c : Kˣ) (v : Fin 4 ⊕ Fin 4 → K) :
    torusHom hu hf huf c v = torusLin f u c v := rfl

theorem torusHom_mem_orthogonalGroup (c : Kˣ) :
    torusHom hu hf huf c ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  set a := ((c : K) - 1) * polar (quadPlus 4 K) v f
  set b := (((c⁻¹ : Kˣ) : K) - 1) * polar (quadPlus 4 K) v u
  have e : torusHom hu hf huf c v = v + (a • u + b • f) := by
    rw [torusHom_apply, torusLin_apply, smul_smul, smul_smul, add_assoc]
  rw [e, QuadraticMap.map_add (quadPlus 4 K) v, QuadraticMap.map_add (quadPlus 4 K) (a • u),
    QuadraticMap.map_smul, QuadraticMap.map_smul, hu, hf, polar_smul_left, polar_smul_right, huf,
    polar_add_right, polar_smul_right, polar_smul_right]
  have hc : (c : K) * ((c⁻¹ : Kˣ) : K) = 1 := by simp
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one, a, b]
  linear_combination (polar (quadPlus 4 K) v u * polar (quadPlus 4 K) v f) * hc

end Torus

theorem exists_torus8 [Finite K] (h2 : (2 : K) = 0) (huw : IsTSLine8 u w) (c : Kˣ) :
    ∃ A : GL8, A ∈ StatedOmega (StatedQuadPlus 4 K) ∧ (A : M8) *ᵥ u = (c : K) • u ∧
      (A : M8) *ᵥ w = w := by
  classical
  haveI := Fintype.ofFinite K
  obtain ⟨x₁, -, h11, h21, -, -⟩ := exists_dual_pair huw
  set f := x₁ - quadPlus 4 K x₁ • u with hfdef
  have hu := quadPlus_u huw
  have hux : polar (quadPlus 4 K) u x₁ = 1 := h11
  have huu : polar (quadPlus 4 K) u u = 0 := by rw [polar_self, hu, smul_zero]
  have hf : quadPlus 4 K f = 0 := by
    rw [hfdef, sub_eq_add_neg, QuadraticMap.map_add (quadPlus 4 K), ← neg_smul,
      QuadraticMap.map_smul, polar_smul_right, hu, polar_comm _ x₁ u, hux]
    simp
  have huf : polar (quadPlus 4 K) u f = 1 := by
    rw [hfdef, polar_sub_right, polar_smul_right, huu, hux, smul_zero, sub_zero]
  have hwf : polar (quadPlus 4 K) w f = 0 := by
    rw [hfdef, polar_sub_right, polar_smul_right, polar_comm _ w u, polar_u_w huw, h21, smul_zero,
      sub_zero]
  let T := torusHom hu hf huf c
  have hodd : Odd (Fintype.card Kˣ) := by
    have hch : ringChar K = 2 := CharP.ringChar_of_prime_eq_zero Nat.prime_two (by exact_mod_cast h2)
    have heven : Fintype.card K % 2 = 0 := FiniteField.even_card_iff_char_two.mp hch
    rw [Fintype.card_units]
    exact Nat.Even.sub_odd Fintype.card_pos (Nat.even_iff.mpr heven) odd_one
  have hpow : T ^ Fintype.card Kˣ = 1 := by
    rw [← map_pow, pow_card_eq_one, map_one]
  have hE : T ∈ elementaryGroup (quadPlus 4 K) :=
    mem_elementaryGroup_quadPlus_of_odd_pow h2 (by norm_num) (torusHom_mem_orthogonalGroup hu hf huf c)
      hodd hpow
  refine ⟨(toLinEquiv (Fin 4 ⊕ Fin 4) K).symm T, ?_, ?_, ?_⟩
  · rw [mem_statedOmega_iff_mem_elementaryGroup (coe_quadPlus 4 K)
      (commutator_orthogonalGroup_quadPlus (by norm_num)), MulEquiv.apply_symm_apply]
    exact hE
  · rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply, torusHom_apply, torusLin_apply, huf, huu]
    simp only [one_smul, zero_smul, smul_zero, add_zero]
    module
  · rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply, torusHom_apply, torusLin_apply, hwf,
      polar_comm _ w u, polar_u_w huw]
    simp

end CFSG.RankThree.GF2n.Stroth80.S715L
