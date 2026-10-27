module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBConjugation
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBStated
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBFieldConjugation
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentNormalization
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.QuadIsotropic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
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
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open LinearMap (BilinForm)
open Module
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatalogueBOrthogonalDescent
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.Open (StatedProj StatedSp)

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_isometry_one_add_sqZero (hK : ringChar K ≠ 2) (B : BilinForm K V)
    (N : Module.End K V) (hN : N ≠ 0) (hNN : N * N = 0)
    (hskew : ∀ x y, B (N x) y = -B x (N y)) :
    ∃ U : isometryGroup B, (∀ x, (U : V ≃ₗ[K] V) x = x + N x) ∧
      QuotientGroup.mk' (scalarSigns B) U ≠ 1 ∧ U ^ ringChar K = 1 := by
  have hNN' : ∀ y, N (N y) = 0 := fun y => by
    have := congrArg (fun f : Module.End K V => f y) hNN
    simpa using this
  have hleft : (1 + N) * (1 - N) = 1 := by
    rw [show (1 + N) * (1 - N) = 1 - N * N by noncomm_ring, hNN, sub_zero]
  have hright : (1 - N) * (1 + N) = 1 := by
    rw [show (1 - N) * (1 + N) = 1 - N * N by noncomm_ring, hNN, sub_zero]
  let U : V ≃ₗ[K] V := LinearEquiv.ofLinear (1 + N) (1 - N)
    (by rw [← Module.End.mul_eq_comp, hleft, ← Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, hright, ← Module.End.one_eq_id])
  have hU : ∀ x, U x = x + N x := fun x => rfl
  have hpow : ∀ n : ℕ, ∀ x, (U ^ n) x = x + (n : K) • N x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', LinearEquiv.mul_apply, hU, ih, map_add, map_smul, hNN']
        simp only [smul_zero, add_zero, Nat.cast_succ, add_smul, one_smul]
        abel
  have hiso : U ∈ isometryGroup B := by
    rw [mem_isometryGroup_iff]
    intro x y
    rw [hU x, hU y]
    have hxs := hskew x y
    have hxy := hskew x (N y)
    rw [hNN'] at hxy
    simp only [map_add, LinearMap.add_apply, map_zero] at hxy ⊢
    rw [hxs, hxy]
    ring
  let U₀ : isometryGroup B := ⟨U, hiso⟩
  refine ⟨U₀, hU, ?_, ?_⟩
  · intro h
    have hmem : U₀ ∈ scalarSigns B := (QuotientGroup.eq_one_iff (N := scalarSigns B) U₀).mp h
    rcases (mem_scalarSigns_iff B U₀).mp hmem with h1 | h1
    ·
      apply hN
      apply LinearMap.ext
      intro x
      have hx : (U : V ≃ₗ[K] V) x = (1 : V ≃ₗ[K] V) x := by
        rw [show (U : V ≃ₗ[K] V) = ((1 : isometryGroup B) : V ≃ₗ[K] V) from
          congrArg (fun z : isometryGroup B => (z : V ≃ₗ[K] V)) h1]
        rfl
      rw [hU x] at hx
      have hx' : N x + x = 0 + x := by
        simpa [add_comm] using hx
      simpa using add_right_cancel hx'
    ·
      have hx2 : ∀ x, N x = (-2 : K) • x := by
        intro x
        have hx : (U : V ≃ₗ[K] V) x = (negIsometry B : V ≃ₗ[K] V) x :=
          congrArg (fun z : isometryGroup B => (z : V ≃ₗ[K] V) x) h1
        rw [hU x, negIsometry_apply] at hx
        have h2 : N x = -x - x := by
          rw [← hx]
          abel
        rw [h2, sub_eq_add_neg, ← neg_add, show (-2 : K) = -(2 : K) by ring, neg_smul,
          two_smul]
      have h4all : ∀ x : V, (4 : K) • x = 0 := by
        intro x
        have h := hNN' x
        rw [hx2, hx2, smul_smul] at h
        rwa [show ((-2 : K) * (-2 : K)) = (4 : K) by ring] at h
      by_cases h4 : (4 : K) = 0
      · have h2 : (2 : K) = 0 := by
          have h4' : (4 : K) = (2 : K) * (2 : K) := by ring
          rw [h4'] at h4
          exact (mul_eq_zero.mp h4).elim id id
        exact Ring.two_ne_zero hK h2
      · apply hN
        apply LinearMap.ext
        intro x
        rcases smul_eq_zero.mp (h4all x) with h | h
        · exact absurd h h4
        · rw [h]
          simp
  · apply Subtype.ext
    rw [Subgroup.coe_pow]
    apply LinearEquiv.ext
    intro x
    rw [hpow, ringChar.Nat.cast_ringChar, zero_smul, add_zero]
    rfl

private def sqZeroT (B : BilinForm K V) (v : V) : Module.End K V :=
  LinearMap.smulRight (B v) v

private def sqZeroC (B : BilinForm K V) (v w : V) : Module.End K V :=
  LinearMap.smulRight (B v) w + LinearMap.smulRight (B w) v

private theorem sqZeroT_apply (B : BilinForm K V) (v x : V) :
    sqZeroT B v x = B v x • v := rfl

private theorem sqZeroC_apply (B : BilinForm K V) (v w x : V) :
    sqZeroC B v w x = B v x • w + B w x • v := rfl

private theorem sqZeroT_skew {B : BilinForm K V} (hB : B.IsAlt) (v : V) :
    ∀ x y, B (sqZeroT B v x) y = -B x (sqZeroT B v y) := by
  intro x y
  simp only [sqZeroT, LinearMap.smulRight_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  rw [show B x v = -B v x from (hB.neg_eq v x).symm]
  ring

private theorem sqZeroC_skew {B : BilinForm K V} (hB : B.IsAlt) (v w : V) :
    ∀ x y, B (sqZeroC B v w x) y = -B x (sqZeroC B v w y) := by
  intro x y
  simp only [sqZeroC, LinearMap.add_apply, LinearMap.smulRight_apply, map_add, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  rw [show B x w = -B w x from (hB.neg_eq w x).symm,
    show B x v = -B v x from (hB.neg_eq v x).symm]
  ring

private theorem sqZeroT_sq {B : BilinForm K V} (hB : B.IsAlt) (v : V) :
    sqZeroT B v * sqZeroT B v = 0 := by
  apply LinearMap.ext
  intro x
  simp [sqZeroT, LinearMap.smulRight_apply, hB.self_eq_zero v]

private theorem sqZeroC_sq {B : BilinForm K V} (hB : B.IsAlt) {v w : V}
    (hvv : B v v = 0) (hww : B w w = 0) (hvw : B v w = 0) :
    sqZeroC B v w * sqZeroC B v w = 0 := by
  apply LinearMap.ext
  intro x
  have hvC : B v (sqZeroC B v w x) = 0 := by
    simp only [sqZeroC, LinearMap.add_apply, LinearMap.smulRight_apply, map_add, map_smul,
      smul_eq_mul]
    rw [hvv, hvw]
    ring
  have hwC : B w (sqZeroC B v w x) = 0 := by
    simp only [sqZeroC, LinearMap.add_apply, LinearMap.smulRight_apply, map_add, map_smul,
      smul_eq_mul]
    rw [hww, show B w v = -B v w from (hB.neg_eq v w).symm, hvw]
    ring
  change sqZeroC B v w (sqZeroC B v w x) = 0
  rw [sqZeroC_apply, hvC, hwC]
  simp

private theorem sqZeroT_ne_zero {B : BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    {v : V} (hv : v ≠ 0) : sqZeroT B v ≠ 0 := by
  intro h
  have hfun : ∀ x, B v x = 0 := by
    intro x
    have hx : sqZeroT B v x = 0 := by rw [h]; rfl
    rw [sqZeroT_apply] at hx
    rcases smul_eq_zero.mp hx with h1 | h1
    · exact h1
    · exact absurd h1 hv
  exact hv ((hB.isRefl.nondegenerate_iff_separatingLeft.mp hnd) v hfun)

private theorem sqZeroC_ne_zero {B : BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    {v w : V} (hv : v ≠ 0) (hvw : ∀ c : K, w ≠ c • v) : sqZeroC B v w ≠ 0 := by
  intro h
  have hBv : ∀ x, B v x = 0 := by
    intro x
    by_contra hx
    have hCx : sqZeroC B v w x = 0 := by rw [h]; rfl
    rw [sqZeroC_apply] at hCx
    have h1 : B v x • w = (-(B w x)) • v := by
      have h0 : B v x • w + B w x • v = 0 := hCx
      calc B v x • w = B v x • w + B w x • v - B w x • v := by abel
        _ = 0 - B w x • v := by rw [h0]
        _ = (-(B w x)) • v := by rw [zero_sub, neg_smul]
    have h2 : w = (B v x)⁻¹ • (B v x • w) := by
      rw [smul_smul, inv_mul_cancel₀ hx, one_smul]
    have hw' : w = ((B v x)⁻¹ * -(B w x)) • v := by
      calc w = (B v x)⁻¹ • (B v x • w) := h2
        _ = (B v x)⁻¹ • ((-(B w x)) • v) := by rw [h1]
        _ = ((B v x)⁻¹ * -(B w x)) • v := by rw [smul_smul]
    exact hvw _ hw'
  exact hv ((hB.isRefl.nondegenerate_iff_separatingLeft.mp hnd) v hBv)

private theorem sqZeroT_sub_smul_ne_zero {B : BilinForm K V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {v w : V} (hvw : ∀ c : K, w ≠ c • v) (d : K) :
    sqZeroT B w - d • sqZeroT B v ≠ 0 := by
  intro h
  have hBw : ∀ x, B w x = 0 := by
    intro x
    by_contra hwx
    have hx : (sqZeroT B w - d • sqZeroT B v) x = 0 := by rw [h]; rfl
    rw [LinearMap.sub_apply, LinearMap.smul_apply, sqZeroT_apply, sqZeroT_apply,
      smul_smul] at hx
    have h1 : B w x • w = (d * B v x) • v := by
      have h0 : B w x • w - (d * B v x) • v = 0 := hx
      exact sub_eq_zero.mp h0
    have h2 : w = (B w x)⁻¹ • (B w x • w) := by
      rw [smul_smul, inv_mul_cancel₀ hwx, one_smul]
    have hw' : w = ((B w x)⁻¹ * (d * B v x)) • v := by
      calc w = (B w x)⁻¹ • (B w x • w) := h2
        _ = (B w x)⁻¹ • ((d * B v x) • v) := by rw [h1]
        _ = ((B w x)⁻¹ * (d * B v x)) • v := by rw [smul_smul]
    exact hvw _ hw'
  exact hvw 0 (by simpa using
    ((hB.isRefl.nondegenerate_iff_separatingLeft.mp hnd) w hBw))

private theorem similitude_adjoint {B : BilinForm K V} {g : V ≃ₗ[K] V} {d μ : Kˣ}
    (hsq : ∀ x, g (g x) = (d : K) • x)
    (hsim : ∀ x y, B (g x) (g y) = (μ : K) * B x y) (x y : V) :
    B (g x) y = ((μ : K) / (d : K)) * B x (g y) := by
  have hy : y = g ((d : K)⁻¹ • g y) := by
    have h := hsq ((d : K)⁻¹ • g y)
    rw [smul_smul, mul_inv_cancel₀ d.ne_zero, one_smul] at h
    exact (g.injective h).symm
  calc B (g x) y = B (g x) (g ((d : K)⁻¹ • g y)) := by conv_lhs => rw [hy]
    _ = (μ : K) * B x ((d : K)⁻¹ • g y) := hsim x _
    _ = (μ : K) * ((d : K)⁻¹ * B x (g y)) := by rw [map_smul, smul_eq_mul]
    _ = ((μ : K) / (d : K)) * B x (g y) := by rw [div_eq_mul_inv]; ring

private theorem sqZeroT_commute_eigen {B : BilinForm K V} {g : V ≃ₗ[K] V} {d μ : Kˣ}
    (hsim : ∀ x y, B (g x) (g y) = (μ : K) * B x y)
    {v : V} {c : K} (hv : g v = c • v) (hc : c * c = (d : K))
    (hμd : (μ : K) = (d : K)) :
    ∀ x, g (sqZeroT B v x) = sqZeroT B v (g x) := by
  intro x
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact d.ne_zero hc.symm
  have hBvgx : B v (g x) = c * B v x := by
    have h := hsim v x
    rw [hv, hμd] at h
    simp only [map_smul] at h
    rw [show (d : K) = c * c from hc.symm, mul_assoc] at h
    exact mul_left_cancel₀ hc0 h
  calc g (sqZeroT B v x) = B v x • g v := by rw [sqZeroT_apply, map_smul]
    _ = B v x • (c • v) := by rw [hv]
    _ = (c * B v x) • v := by rw [smul_smul, mul_comm]
    _ = B v (g x) • v := by rw [hBvgx]
    _ = sqZeroT B v (g x) := by rw [sqZeroT_apply]

private theorem sqZeroC_commute_paired {B : BilinForm K V} {g : V ≃ₗ[K] V} {d μ : Kˣ}
    (hsim : ∀ x y, B (g x) (g y) = (μ : K) * B x y)
    {e f : V} {a : K} (he : g e = a • e) (hf : g f = -a • f)
    (ha : a * a = (d : K)) (hμd : (μ : K) = -(d : K)) :
    ∀ x, g (sqZeroC B e f x) = sqZeroC B e f (g x) := by
  intro x
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, mul_zero] at ha
    exact d.ne_zero ha.symm
  have hBe : B e (g x) = -a * B e x := by
    have h := hsim e x
    rw [he, hμd] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [show -(d : K) = -(a * a) from by rw [ha]] at h
    have h' : a * B e (g x) = a * (-a * B e x) := by
      rw [h]
      ring
    exact mul_left_cancel₀ ha0 h'
  have hBf : B f (g x) = a * B f x := by
    have h := hsim f x
    rw [hf, hμd] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [show -(d : K) = -(a * a) from by rw [ha]] at h
    have h' : (-a) * B f (g x) = (-a) * (a * B f x) := by
      rw [h]
      ring
    exact mul_left_cancel₀ (neg_ne_zero.mpr ha0) h'
  calc g (sqZeroC B e f x) = B e x • g f + B f x • g e := by
        rw [sqZeroC_apply, map_add, map_smul, map_smul]
    _ = B e x • (-a • f) + B f x • (a • e) := by rw [he, hf]
    _ = (-a * B e x) • f + (a * B f x) • e := by
        rw [smul_smul, smul_smul]
        congr 2 <;> ring
    _ = B e (g x) • f + B f (g x) • e := by rw [hBe, hBf]
    _ = sqZeroC B e f (g x) := by rw [sqZeroC_apply]

private theorem sqZeroC_commute_self {B : BilinForm K V} {g : V ≃ₗ[K] V} {d μ : Kˣ}
    (hsq : ∀ x, g (g x) = (d : K) • x)
    (hsim : ∀ x y, B (g x) (g y) = (μ : K) * B x y)
    {v : V} (hμd : (μ : K) = (d : K)) :
    ∀ x, g (sqZeroC B v (g v) x) = sqZeroC B v (g v) (g x) := by
  intro x
  have hratio : (μ : K) / (d : K) = 1 := by rw [hμd, div_self d.ne_zero]
  have h1 : B v (g x) = B (g v) x := by
    have h := similitude_adjoint hsq hsim v x
    rw [hratio, one_mul] at h
    exact h.symm
  have h2 : B (g v) (g x) = (d : K) * B v x := by
    have h := similitude_adjoint hsq hsim (g v) x
    rw [hratio, one_mul] at h
    have hA : B (g (g v)) x = (d : K) * B v x := by
      rw [hsq, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hA] at h
    exact h.symm
  calc g (sqZeroC B v (g v) x)
      = B v x • g (g v) + B (g v) x • g v := by
        rw [sqZeroC_apply, map_add, map_smul, map_smul]
    _ = B v x • ((d : K) • v) + B (g v) x • (g v) := by rw [hsq]
    _ = ((d : K) * B v x) • v + B (g v) x • (g v) := by rw [smul_smul, mul_comm]
    _ = B (g v) (g x) • v + B v (g x) • (g v) := by rw [h2, h1]
    _ = sqZeroC B v (g v) (g x) := by rw [sqZeroC_apply, add_comm]

private theorem sqZeroT_sub_commute {B : BilinForm K V} {g : V ≃ₗ[K] V} {d μ : Kˣ}
    (hsq : ∀ x, g (g x) = (d : K) • x)
    (hsim : ∀ x y, B (g x) (g y) = (μ : K) * B x y)
    {v : V} (hμd : (μ : K) = -(d : K)) :
    ∀ x, g ((sqZeroT B (g v) - (d : K) • sqZeroT B v) x)
      = (sqZeroT B (g v) - (d : K) • sqZeroT B v) (g x) := by
  intro x
  have hratio : (μ : K) / (d : K) = -1 := by
    rw [hμd, neg_div, div_self d.ne_zero]
  have h1 : B v (g x) = -B (g v) x := by
    have h := similitude_adjoint hsq hsim v x
    rw [hratio, neg_one_mul] at h
    have h' : -B (g v) x = B v (g x) := by rw [h]; simp
    exact h'.symm
  have h2 : B (g v) (g x) = -((d : K) * B v x) := by
    have h := similitude_adjoint hsq hsim (g v) x
    rw [hratio, neg_one_mul] at h
    have hA : B (g (g v)) x = (d : K) * B v x := by
      rw [hsq, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have h' : -(B (g (g v)) x) = B (g v) (g x) := by rw [h]; simp
    calc B (g v) (g x) = -(B (g (g v)) x) := h'.symm
      _ = -((d : K) * B v x) := congrArg Neg.neg hA
  have hNx : (sqZeroT B (g v) - (d : K) • sqZeroT B v) x
      = B (g v) x • (g v) - ((d : K) * B v x) • v := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, sqZeroT_apply, sqZeroT_apply, smul_smul]
  have hNgx : (sqZeroT B (g v) - (d : K) • sqZeroT B v) (g x)
      = B (g v) (g x) • (g v) - ((d : K) * B v (g x)) • v := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, sqZeroT_apply, sqZeroT_apply, smul_smul]
  calc g ((sqZeroT B (g v) - (d : K) • sqZeroT B v) x)
      = B (g v) x • g (g v) - ((d : K) * B v x) • g v := by
        rw [hNx, map_sub, map_smul, map_smul]
    _ = B (g v) x • ((d : K) • v) - ((d : K) * B v x) • (g v) := by rw [hsq]
    _ = ((d : K) * B (g v) x) • v - ((d : K) * B v x) • (g v) := by
        rw [smul_smul, mul_comm (B (g v) x) (d : K)]
    _ = (sqZeroT B (g v) - (d : K) • sqZeroT B v) (g x) := by
        rw [hNgx, h2, h1, mul_neg, neg_smul]
        simp only [neg_smul]
        abel

private theorem eigen_isCompl [FiniteDimensional K V] {g : V ≃ₗ[K] V} {a d : K}
    (h2 : (2 : K) ≠ 0) (ha0 : a ≠ 0) (had : d = a * a)
    (hsq : ∀ x, g (g x) = d • x) :
    IsCompl (LinearMap.ker ((g : Module.End K V) - a • 1))
      (LinearMap.ker ((g : Module.End K V) + a • 1)) := by
  set Wp : Submodule K V := LinearMap.ker ((g : Module.End K V) - a • 1) with hWpdef
  set Wm : Submodule K V := LinearMap.ker ((g : Module.End K V) + a • 1) with hWmdef
  have hPQ : ((g : Module.End K V) - a • 1) * ((g : Module.End K V) + a • 1) = 0 := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply]
    change (g : Module.End K V) ((g : Module.End K V) x + a • x) -
      a • ((g : Module.End K V) x + a • x) = 0
    rw [map_add, map_smul, smul_add,
      show (g : Module.End K V) ((g : Module.End K V) x) = d • x from hsq x, had, smul_smul]
    abel
  have hQP : ((g : Module.End K V) + a • 1) * ((g : Module.End K V) - a • 1) = 0 := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply]
    change (g : Module.End K V) ((g : Module.End K V) x - a • x) +
      a • ((g : Module.End K V) x - a • x) = 0
    rw [map_sub, map_smul, smul_sub,
      show (g : Module.End K V) ((g : Module.End K V) x) = d • x from hsq x, had, smul_smul]
    abel
  have hdisj : Disjoint Wp Wm := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have h1 : g x = a • x := by
      have := hx1
      simpa [Wp, LinearMap.mem_ker, sub_eq_zero] using this
    have h2' : g x = -a • x := by
      have := hx2
      simpa [Wm, LinearMap.mem_ker, add_eq_zero_iff_eq_neg] using this
    have h3 : a • x = -a • x := by rw [← h1, h2']
    have h4 : (a + a) • x = 0 := by
      have h5 : a • x + a • x = 0 := by
        nth_rewrite 2 [h3]
        simp
      simpa [add_smul] using h5
    have haa : a + a ≠ 0 := by
      have h : a + a = (2 : K) * a := by ring
      rw [h]
      exact mul_ne_zero h2 ha0
    exact (smul_eq_zero.mp h4).resolve_left haa
  have hle : finrank K V ≤ finrank K Wp + finrank K Wm := by
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((g : Module.End K V) - a • 1) (V₂ := V)
    have h2' : finrank K (LinearMap.range ((g : Module.End K V) - a • 1)) ≤
        finrank K Wm := by
      apply Submodule.finrank_mono
      rintro y ⟨x, rfl⟩
      have h := congrArg (fun f : Module.End K V => f x) hQP
      simpa [Wm, LinearMap.mem_ker, Module.End.mul_apply, LinearMap.sub_apply,
        LinearMap.add_apply, LinearMap.smul_apply] using h
    have h3' : finrank K (LinearMap.ker ((g : Module.End K V) - a • 1)) = finrank K Wp := rfl
    omega
  exact (Submodule.isCompl_iff_disjoint Wp Wm hle).mpr hdisj

private theorem eigen_isotropic {B : BilinForm K V} {g : V ≃ₗ[K] V} {s d μ : K}
    (hsim : ∀ x y, B (g x) (g y) = μ * B x y) (h2 : (2 : K) ≠ 0)
    (hsd : s * s = d) (hd0 : d ≠ 0) (hμ : μ = -d) {W : Submodule K V}
    (hW : ∀ x, x ∈ W ↔ g x = s • x) :
    ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by
  intro x hx y hy
  have hx' : g x = s • x := (hW x).mp hx
  have hy' : g y = s • y := (hW y).mp hy
  have hB1 : B (s • x) = s • B x := LinearMap.map_smul B s x
  have hB2 : B x (s • y) = s • B x y := LinearMap.map_smul (B x) s y
  have hBs : B (s • x) (s • y) = (s * s) * B x y := by
    rw [hB1, LinearMap.smul_apply, hB2, smul_smul, smul_eq_mul]
  have h := hsim x y
  rw [hx', hy', hBs, hsd, hμ] at h
  have h0 : (2 : K) * (d * B x y) = 0 := by
    have h1 : d * B x y + d * B x y = 0 := by
      nth_rewrite 2 [h]
      simp
    simpa [two_mul] using h1
  have h2d : (2 : K) * d ≠ 0 := mul_ne_zero h2 hd0
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact absurd h' h2
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' hd0
    · exact h''

private theorem eigen_finrank_eq [FiniteDimensional K V] {B : BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) {Wp Wm : Submodule K V} (hcompl : IsCompl Wp Wm)
    (hisop : ∀ x ∈ Wp, ∀ y ∈ Wp, B x y = 0)
    (hisom : ∀ x ∈ Wm, ∀ y ∈ Wm, B x y = 0) :
    finrank K Wp = finrank K Wm := by
  have hle1 : finrank K Wp ≤ finrank K Wm := by
    let φ : Wp →ₗ[K] (Wm →ₗ[K] K) :=
      { toFun := fun e => (B (e : V)).comp Wm.subtype
        map_add' := by
          intro e1 e2
          ext m
          simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_add,
            LinearMap.map_add]
        map_smul' := by
          intro c e
          ext m
          simp only [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul,
            LinearMap.map_smul, RingHom.id_apply] }
    have hker : ∀ e : Wp, φ e = 0 → e = 0 := by
      intro e he
      have hBm : ∀ m ∈ Wm, B (e : V) m = 0 := by
        intro m hm
        have h := congrArg (fun f : Wm →ₗ[K] K => f ⟨m, hm⟩) he
        simpa [φ] using h
      have hBp : ∀ p ∈ Wp, B (e : V) p = 0 := fun p hp => hisop e e.2 p hp
      have hBall : ∀ v : V, B (e : V) v = 0 := by
        intro v
        have hv : v ∈ Wp ⊔ Wm := by rw [hcompl.sup_eq_top]; trivial
        rcases Submodule.mem_sup.mp hv with ⟨p, hp, m, hm, rfl⟩
        rw [map_add, hBp p hp, hBm m hm, add_zero]
      have hz : (e : V) = 0 := (hB.isRefl.nondegenerate_iff_separatingLeft.mp hnd) e hBall
      exact Subtype.ext hz
    have hinj : Function.Injective φ := by
      intro e1 e2 h
      have hsub : φ (e1 - e2) = 0 := by rw [map_sub, h, sub_self]
      have hz := hker (e1 - e2) hsub
      exact sub_eq_zero.mp hz
    have h1 := LinearMap.finrank_le_finrank_of_injective (f := φ) hinj
    rwa [Module.finrank_linearMap, Module.finrank_self, mul_one] at h1
  have hle2 : finrank K Wm ≤ finrank K Wp := by
    let ψ : Wm →ₗ[K] (Wp →ₗ[K] K) :=
      { toFun := fun f => (B (f : V)).comp Wp.subtype
        map_add' := by
          intro f1 f2
          ext m
          simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_add,
            LinearMap.map_add]
        map_smul' := by
          intro c f
          ext m
          simp only [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul,
            LinearMap.map_smul, RingHom.id_apply] }
    have hker : ∀ f : Wm, ψ f = 0 → f = 0 := by
      intro f hf
      have hBp : ∀ p ∈ Wp, B (f : V) p = 0 := by
        intro p hp
        have h := congrArg (fun g : Wp →ₗ[K] K => g ⟨p, hp⟩) hf
        simpa [ψ] using h
      have hBm : ∀ m ∈ Wm, B (f : V) m = 0 := fun m hm => hisom f f.2 m hm
      have hBall : ∀ v : V, B (f : V) v = 0 := by
        intro v
        have hv : v ∈ Wp ⊔ Wm := by rw [hcompl.sup_eq_top]; trivial
        rcases Submodule.mem_sup.mp hv with ⟨p, hp, m, hm, rfl⟩
        rw [map_add, hBp p hp, hBm m hm, add_zero]
      have hz : (f : V) = 0 := (hB.isRefl.nondegenerate_iff_separatingLeft.mp hnd) f hBall
      exact Subtype.ext hz
    have hinj : Function.Injective ψ := by
      intro f1 f2 h
      have hsub : ψ (f1 - f2) = 0 := by rw [map_sub, h, sub_self]
      have hz := hker (f1 - f2) hsub
      exact sub_eq_zero.mp hz
    have h1 := LinearMap.finrank_le_finrank_of_injective (f := ψ) hinj
    rwa [Module.finrank_linearMap, Module.finrank_self, mul_one] at h1
  exact le_antisymm hle1 hle2

private theorem exists_ne_mem_ker_of_two_le [FiniteDimensional K V] {W : Submodule K V}
    (hW : 2 ≤ finrank K W) (φ : W →ₗ[K] K) :
    ∃ f : W, f ≠ 0 ∧ φ f = 0 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker φ (V₂ := K)
  have h2 : finrank K (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    rwa [Module.finrank_self] at this
  have h3 : 0 < finrank K (LinearMap.ker φ) := by omega
  have hne : LinearMap.ker φ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h3
    omega
  obtain ⟨f, hf, hfne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨f, hfne, LinearMap.mem_ker.mp hf⟩

private theorem exists_eigenvector_of_sq [Nontrivial V] {g : V ≃ₗ[K] V} {a d : K}
    (h2 : (2 : K) ≠ 0) (had : d = a * a) (hsq : ∀ x, g (g x) = d • x) :
    ∃ v : V, v ≠ 0 ∧ ∃ c : K, g v = c • v ∧ c * c = d := by
  have hPQ : ((g : Module.End K V) - a • 1) * ((g : Module.End K V) + a • 1) = 0 := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply]
    change (g : Module.End K V) ((g : Module.End K V) x + a • x) -
      a • ((g : Module.End K V) x + a • x) = 0
    rw [map_add, map_smul, smul_add,
      show (g : Module.End K V) ((g : Module.End K V) x) = d • x from hsq x, had, smul_smul]
    abel
  have hQP : ((g : Module.End K V) + a • 1) * ((g : Module.End K V) - a • 1) = 0 := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply]
    change (g : Module.End K V) ((g : Module.End K V) x - a • x) +
      a • ((g : Module.End K V) x - a • x) = 0
    rw [map_sub, map_smul, smul_sub,
      show (g : Module.End K V) ((g : Module.End K V) x) = d • x from hsq x, had, smul_smul]
    abel
  have hsum : ((g : Module.End K V) - a • 1) + ((g : Module.End K V) + a • 1) =
      (2 : K) • (g : Module.End K V) := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [two_smul]
    abel
  have hg0 : (g : Module.End K V) ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hx0 : g x = 0 := by
      have h' := congrArg (fun f : Module.End K V => f x) h
      simpa using h'
    exact hx (g.injective (by simpa using hx0))
  have hP0 : ((g : Module.End K V) - a • 1) ≠ 0 ∨
      ((g : Module.End K V) + a • 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hg0
    have hzero : (2 : K) • (g : Module.End K V) = 0 := by
      rw [← hsum, h.1, h.2, add_zero]
    exact (smul_eq_zero.mp hzero).resolve_left h2
  rcases hP0 with hP | hQ
  · have hex : ∃ x : V, ((g : Module.End K V) - a • 1) x ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (LinearMap.ext h)
    obtain ⟨x, hx⟩ := hex
    have hQv : ((g : Module.End K V) + a • 1) (((g : Module.End K V) - a • 1) x) = 0 := by
      have := congrArg (fun f : Module.End K V => f x) hQP
      simpa [Module.End.mul_apply] using this
    have hgv : g (((g : Module.End K V) - a • 1) x) = -a • (((g : Module.End K V) - a • 1) x) := by
      have h := hQv
      rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at h
      have h' : g (((g : Module.End K V) - a • 1) x) +
          a • (((g : Module.End K V) - a • 1) x) = 0 := h
      simpa [neg_smul] using eq_neg_of_add_eq_zero_left h'
    refine ⟨((g : Module.End K V) - a • 1) x, hx, -a, hgv, ?_⟩
    rw [show (-a) * (-a) = a * a by ring, ← had]
  · have hex : ∃ x : V, ((g : Module.End K V) + a • 1) x ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ (LinearMap.ext h)
    obtain ⟨x, hx⟩ := hex
    have hPv : ((g : Module.End K V) - a • 1) (((g : Module.End K V) + a • 1) x) = 0 := by
      have := congrArg (fun f : Module.End K V => f x) hPQ
      simpa [Module.End.mul_apply] using this
    have hgv : g (((g : Module.End K V) + a • 1) x) = a • (((g : Module.End K V) + a • 1) x) := by
      have h := hPv
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h
      exact sub_eq_zero.mp h
    exact ⟨((g : Module.End K V) + a • 1) x, hx, a, hgv, had.symm⟩

private theorem not_isSquare_of_eigen {g : V ≃ₗ[K] V} {d : K}
    (hsq : ∀ x, g (g x) = d • x) {v : V} (hv : v ≠ 0) (hnsq : ¬ IsSquare d) (c : K) :
    g v ≠ c • v := by
  intro h
  apply hnsq
  have h2 : d • v = (c * c) • v := by
    calc d • v = g (g v) := (hsq v).symm
      _ = g (c • v) := by rw [h]
      _ = c • g v := by rw [map_smul]
      _ = c • (c • v) := by rw [h]
      _ = (c * c) • v := by rw [smul_smul]
  have h3 : (d - c * c) • v = 0 := by rw [sub_smul, h2, sub_self]
  have h4 : d - c * c = 0 := (smul_eq_zero.mp h3).resolve_right hv
  exact ⟨c, sub_eq_zero.mp h4⟩

private theorem sqZeroT_sub_smul_sq {B : BilinForm K V} (hB : B.IsAlt) {v w : V}
    (hvv : B v v = 0) (hww : B w w = 0) (hvw : B v w = 0) (d : K) :
    (sqZeroT B w - d • sqZeroT B v) * (sqZeroT B w - d • sqZeroT B v) = 0 := by
  apply LinearMap.ext
  intro x
  have hNx : (sqZeroT B w - d • sqZeroT B v) x = B w x • w - (d * B v x) • v := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, sqZeroT_apply, sqZeroT_apply, smul_smul]
  have hvN : B v (B w x • w - (d * B v x) • v) = 0 := by
    rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hvv, hvw]
    ring
  have hwN : B w (B w x • w - (d * B v x) • v) = 0 := by
    rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hww,
      show B w v = -B v w from (hB.neg_eq v w).symm, hvw]
    ring
  change (sqZeroT B w - d • sqZeroT B v) ((sqZeroT B w - d • sqZeroT B v) x) = 0
  rw [hNx, LinearMap.sub_apply, LinearMap.smul_apply, sqZeroT_apply, sqZeroT_apply,
    hwN, hvN]
  simp

theorem exists_sqZero_commute_similitude [Finite K] (hK : ringChar K ≠ 2)
    [FiniteDimensional K V] (hdim : 4 ≤ Module.finrank K V) (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (g : V ≃ₗ[K] V) (d μ : Kˣ) (hsq : ∀ x, g (g x) = (d : K) • x)
    (hsim : ∀ x y, B (g x) (g y) = (μ : K) * B x y) :
    ∃ N : Module.End K V, N ≠ 0 ∧ N * N = 0 ∧ (∀ x y, B (N x) y = -B x (N y)) ∧
      ∀ x, g (N x) = N (g x) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
  have hBne : B ≠ 0 := hnd.ne_zero
  have hex : ∃ x y, B x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hBne (by ext x y; exact h x y)
  obtain ⟨x, y, hxy⟩ := hex
  have hs : (d : K) * (d : K) = (μ : K) * (μ : K) := by
    have h := hsim (g x) (g y)
    rw [hsq, hsq] at h
    have hL : B ((d : K) • x) ((d : K) • y) = (d : K) * ((d : K) * B x y) := by
      have h1 : B ((d : K) • x) = (d : K) • B x := LinearMap.map_smul B (d : K) x
      have h2 : B x ((d : K) • y) = (d : K) • B x y :=
        LinearMap.map_smul (B x) (d : K) y
      rw [h1, LinearMap.smul_apply, h2, smul_eq_mul, smul_eq_mul]
    rw [hL, hsim x y] at h
    have h' : ((d : K) * (d : K)) * B x y = ((μ : K) * (μ : K)) * B x y := by
      rw [mul_assoc, mul_assoc]
      exact h
    exact mul_right_cancel₀ hxy h'
  have hμd : (μ : K) = (d : K) ∨ (μ : K) = -(d : K) := by
    have hsq2 : (μ : K) ^ 2 = (d : K) ^ 2 := by
      rw [sq, sq]
      exact hs.symm
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq2
  by_cases hsqd : IsSquare (d : K)
  ·
    obtain ⟨a, ha⟩ := hsqd
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, mul_zero] at ha
      exact d.ne_zero ha
    rcases hμd with hμ | hμ
    ·
      obtain ⟨v, hvne, c, hv, hc⟩ := exists_eigenvector_of_sq h2 ha hsq
      exact ⟨sqZeroT B v, sqZeroT_ne_zero hB hnd hvne, sqZeroT_sq hB v,
        sqZeroT_skew hB v, sqZeroT_commute_eigen hsim hv hc hμ⟩
    ·
      let Wp : Submodule K V := LinearMap.ker ((g : Module.End K V) - a • 1)
      let Wm : Submodule K V := LinearMap.ker ((g : Module.End K V) + a • 1)
      have hWp : ∀ x, x ∈ Wp ↔ g x = a • x := by
        intro z
        simp [Wp, LinearMap.mem_ker, sub_eq_zero]
      have hWm : ∀ x, x ∈ Wm ↔ g x = -a • x := by
        intro z
        simp [Wm, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]
      have hcompl : IsCompl Wp Wm := eigen_isCompl h2 ha0 ha hsq
      have hisop : ∀ x ∈ Wp, ∀ y ∈ Wp, B x y = 0 :=
        eigen_isotropic hsim h2 ha.symm d.ne_zero hμ hWp
      have hneg : (-a) * (-a) = (d : K) := by
        rw [show (-a) * (-a) = a * a by ring, ← ha]
      have hisom : ∀ x ∈ Wm, ∀ y ∈ Wm, B x y = 0 :=
        eigen_isotropic hsim h2 hneg d.ne_zero hμ hWm
      have hfr : finrank K Wp = finrank K Wm := eigen_finrank_eq hB hnd hcompl hisop hisom
      have hdimW : finrank K Wp + finrank K Wm = finrank K V :=
        Submodule.finrank_add_eq_of_isCompl hcompl
      have hWm2 : 2 ≤ finrank K Wm := by omega
      have hWp2 : 2 ≤ finrank K Wp := by omega
      have hWpne : Wp ≠ ⊥ := by
        intro h
        rw [h, finrank_bot] at hWp2
        omega
      obtain ⟨e, heWp, hene⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWpne
      let φ : Wm →ₗ[K] K := (B e).comp Wm.subtype
      obtain ⟨f, hfne, hf0⟩ := exists_ne_mem_ker_of_two_le (W := Wm) hWm2 φ
      have hfWm : (f : V) ∈ Wm := f.2
      have hfVne : (f : V) ≠ 0 := fun h => hfne (Subtype.ext h)
      have hBe : B e (f : V) = 0 := hf0
      have hfe : ∀ c : K, (f : V) ≠ c • e := by
        intro c hc
        have hmem' : (f : V) ∈ Wp := by
          rw [hc]
          exact Wp.smul_mem c heWp
        exact hfVne (Submodule.disjoint_def.mp hcompl.disjoint (f : V) hmem' hfWm)
      have hee : B e e = 0 := hisop e heWp e heWp
      have hff : B (f : V) (f : V) = 0 := hisom f hfWm f hfWm
      have hef : g e = a • e := (hWp e).mp heWp
      have hff' : g (f : V) = -a • (f : V) := (hWm (f : V)).mp hfWm
      exact ⟨sqZeroC B e (f : V), sqZeroC_ne_zero hB hnd hene hfe,
        sqZeroC_sq hB hee hff hBe, sqZeroC_skew hB e (f : V),
        sqZeroC_commute_paired hsim hef hff' ha.symm hμ⟩
  ·
    by_cases hμ : (μ : K) = (d : K)
    ·
      obtain ⟨v, hvne⟩ := exists_ne (0 : V)
      have hBvw : B v (g v) = 0 := by
        have h1 : B (g v) v = B v (g v) := by
          have h := similitude_adjoint hsq hsim v v
          rw [hμ, div_self d.ne_zero, one_mul] at h
          exact h
        have h2' : B (g v) v = -B v (g v) := (hB.neg_eq v (g v)).symm
        have h3 : B v (g v) = -B v (g v) := h1.symm.trans h2'
        have h4 : (2 : K) * B v (g v) = 0 := by
          have h5 : B v (g v) + B v (g v) = 0 := by
            nth_rewrite 2 [h3]
            simp
          simpa [two_mul] using h5
        rcases mul_eq_zero.mp h4 with h | h
        · exact absurd h h2
        · exact h
      have hww : B (g v) (g v) = 0 := by
        rw [hsim v v, hB.self_eq_zero v, mul_zero]
      have hind : ∀ c : K, g v ≠ c • v := fun c => not_isSquare_of_eigen hsq hvne hsqd c
      exact ⟨sqZeroC B v (g v), sqZeroC_ne_zero hB hnd hvne hind,
        sqZeroC_sq hB (hB.self_eq_zero v) hww hBvw, sqZeroC_skew hB v (g v),
        sqZeroC_commute_self hsq hsim hμ⟩
    ·
      have : Fintype K := Fintype.ofFinite K
      have : DecidableEq K := Classical.decEq K
      let b := Module.finBasis K V
      let D : BilinForm K V := LinearMap.mk₂ K (fun p q => B p (g q))
        (fun p p' q => by simp)
        (fun c p q => by simp)
        (fun p q q' => by simp)
        (fun c p q => by simp)
      let M : Matrix (Fin (finrank K V)) (Fin (finrank K V)) K := BilinForm.toMatrix b D
      have hcard : 3 ≤ Fintype.card (Fin (finrank K V)) := by
        rw [Fintype.card_fin]
        omega
      obtain ⟨c, hcne, hc0⟩ :=
        CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.exists_isotropic_of_three_le
          (K := K) (ι := Fin (finrank K V)) hcard M
      let v : V := b.equivFun.symm c
      have hvc : b.equivFun v = c := LinearEquiv.apply_symm_apply _ _
      have hvne : v ≠ 0 := by
        intro h
        apply hcne
        rw [← hvc, h]
        simp
      have hDv : D v v = 0 := by
        have h := BilinForm.dotProduct_toMatrix_mulVec b D c c
        rw [← h]
        exact hc0
      have hBvw : B v (g v) = 0 := hDv
      have hww : B (g v) (g v) = 0 := by
        rw [hsim v v, hB.self_eq_zero v, mul_zero]
      have hind : ∀ c : K, g v ≠ c • v := fun c => not_isSquare_of_eigen hsq hvne hsqd c
      let N : Module.End K V := sqZeroT B (g v) - (d : K) • sqZeroT B v
      have hN : N ≠ 0 := sqZeroT_sub_smul_ne_zero hB hnd hind (d : K)
      have hNN : N * N = 0 :=
        sqZeroT_sub_smul_sq hB (hB.self_eq_zero v) hww hBvw (d : K)
      have hskew : ∀ p q, B (N p) q = -B p (N q) := by
        intro p q
        have h1 := sqZeroT_skew hB (g v) p q
        have h2 := sqZeroT_skew hB v p q
        have hNp : N p = sqZeroT B (g v) p - (d : K) • sqZeroT B v p := rfl
        have hNq : N q = sqZeroT B (g v) q - (d : K) • sqZeroT B v q := rfl
        have hL : B (N p) q = B (sqZeroT B (g v) p) q -
            (d : K) * B (sqZeroT B v p) q := by
          rw [hNp, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
            smul_eq_mul]
        have hR : B p (N q) = B p (sqZeroT B (g v) q) -
            (d : K) * B p (sqZeroT B v q) := by
          rw [hNq, map_sub, map_smul, smul_eq_mul]
        rw [hL, hR, h1, h2]
        ring
      have hμneg : (μ : K) = -(d : K) := by
        rcases hμd with h | h
        · exact absurd h hμ
        · exact h
      refine ⟨N, hN, hNN, hskew, ?_⟩
      exact sqZeroT_sub_commute hsq hsim hμneg

theorem exists_sqZero_commute_semilinear [Finite K] [Nontrivial V] (B : BilinForm K V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (σ : K ≃+* K) (hσ : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (T : V ≃+ V) (d μ : Kˣ) (hsemi : ∀ (a : K) (x : V), T (a • x) = σ a • T x)
    (hsq : ∀ x, T (T x) = (d : K) • x) (hsim : ∀ x y, B (T x) (T y) = (μ : K) * σ (B x y)) :
    ∃ N : Module.End K V, N ≠ 0 ∧ N * N = 0 ∧ (∀ x y, B (N x) y = -B x (N y)) ∧
      ∀ x, T (N x) = N (T x) := by
  have hσσ : ∀ c : K, σ (σ c) = c := by
    intro c
    have h := congrArg (fun τ : K ≃+* K => τ c) hσ
    simpa [pow_two] using h
  have hd : σ (d : K) = (d : K) := square_scalar_fixed σ T (d : K) hsemi hsq
  have hμ : (μ : K) * σ (μ : K) = (d : K) ^ 2 :=
    square_multiplier_identity σ hσ B hnd T (μ : K) (d : K) hsim hsq
  obtain ⟨b, c, hb, hc⟩ := exists_normalizing_units σ hσ hσ1 μ d hd hμ
  have hc' : σ (c : K) = (c : K) * (b : K) ^ 2 * (μ : K) := by
    have h := hc
    rw [div_eq_iff c.ne_zero] at h
    rw [h]
    ring
  have hR : ∀ x, normalizedOperator T b (normalizedOperator T b x) = x :=
    normalizedOperator_involutive σ T d b hsemi hsq hb
  have key : ∀ v : V, v ≠ 0 → (b : K) • T v = v →
      ∃ N : Module.End K V, N ≠ 0 ∧ N * N = 0 ∧
        (∀ x y, B (N x) y = -B x (N y)) ∧ ∀ x, T (N x) = N (T x) := by
    intro v hvne hTvv
    have hTv : T v = (b : K)⁻¹ • v := by
      calc T v = (b : K)⁻¹ • ((b : K) • T v) := by
            rw [smul_smul, inv_mul_cancel₀ b.ne_zero, one_smul]
        _ = (b : K)⁻¹ • v := by rw [hTvv]
    have hTbinv : T ((b : K)⁻¹ • v) = (d : K) • v := by
      rw [hsemi, hTv, smul_smul, map_inv₀, ← mul_inv_rev, hb, inv_inv]
    have hsb : σ (b : K) ≠ 0 := by
      simp
    have hBvTx : ∀ x, B v (T x) = (b : K) * (μ : K) * σ (B v x) := by
      intro x
      have h := hsim ((b : K)⁻¹ • v) x
      rw [hTbinv] at h
      have h2 : (d : K) * B v (T x) = (μ : K) * ((σ (b : K))⁻¹ * σ (B v x)) := by
        have h' := h
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_smul, LinearMap.smul_apply,
          smul_eq_mul, map_mul, map_inv₀] at h'
        exact h'
      calc B v (T x) = (d : K)⁻¹ * ((μ : K) * ((σ (b : K))⁻¹ * σ (B v x))) := by
            rw [← h2]
            field_simp
        _ = ((b : K) * σ (b : K)) * ((μ : K) * ((σ (b : K))⁻¹ * σ (B v x))) := by
            rw [hb]
        _ = (b : K) * (μ : K) * σ (B v x) := by
            rw [show ((b : K) * σ (b : K)) *
                  ((μ : K) * ((σ (b : K))⁻¹ * σ (B v x))) =
                (b : K) * ((σ (b : K)) * (σ (b : K))⁻¹) *
                  ((μ : K) * σ (B v x)) by ring]
            rw [mul_inv_cancel₀ hsb, mul_one]
            ring
    let Tv : Module.End K V := LinearMap.smulRight (B v) v
    let N : Module.End K V := (c : K) • Tv
    have hN : N ≠ 0 := by
      intro h
      have hTv0 : Tv = 0 := by
        have h1 : (c : K)⁻¹ • N = (c : K)⁻¹ • (0 : Module.End K V) := by rw [h]
        simpa [N, smul_smul, inv_mul_cancel₀ c.ne_zero] using h1
      have hBv : ∀ n, B v n = 0 := by
        intro n
        have h2 : Tv n = 0 := by rw [hTv0]; rfl
        rcases smul_eq_zero.mp h2 with h3 | h3
        · exact h3
        · exact absurd h3 hvne
      exact hvne ((hB.isRefl.nondegenerate_iff_separatingLeft.mp hnd) v hBv)
    have hNN : N * N = 0 := by
      apply LinearMap.ext
      intro x
      simp [N, Tv, LinearMap.smulRight_apply, hB.self_eq_zero v]
    have hskew : ∀ x y, B (N x) y = -B x (N y) := by
      intro x y
      have h1 : B (N x) y = (c : K) * B v x * B v y := by
        simp only [N, Tv, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul]
        ring
      have h2 : B x (N y) = (c : K) * B v y * B x v := by
        simp only [N, Tv, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul]
        ring
      have hxv : B x v = -B v x := (hB.neg_eq v x).symm
      rw [h1, h2, hxv]
      ring
    have hcomm : ∀ x, T (N x) = N (T x) := by
      intro x
      have hL : T (N x) = (σ (c : K) * σ (B v x)) • T v := by
        rw [show N x = (c : K) • ((B v x) • v) by rfl, hsemi, hsemi, smul_smul]
      rw [hL, hTv, smul_smul]
      rw [show N (T x) = (c : K) • ((B v (T x)) • v) by rfl, hBvTx, smul_smul]
      congr 1
      rw [hc']
      field_simp [b.ne_zero]
    exact ⟨N, hN, hNN, hskew, hcomm⟩
  obtain ⟨x0, hx0⟩ := exists_ne (0 : V)
  by_cases hx : x0 + normalizedOperator T b x0 = 0
  ·
    obtain ⟨a, ha⟩ : ∃ a : K, σ a ≠ a := by
      by_contra h
      push Not at h
      exact hσ1 (RingEquiv.ext h)
    let δ : K := a - σ a
    have hδ : σ δ = -δ := by
      dsimp only [δ]
      rw [map_sub, hσσ]
      ring
    have hδ0 : δ ≠ 0 := by
      intro h0
      apply ha
      have h1 : a = σ a := sub_eq_zero.mp h0
      exact h1.symm
    have hbTx0 : (b : K) • T x0 = -x0 := by
      have h := hx
      rw [normalizedOperator_apply] at h
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h
    have hvne : δ • x0 ≠ 0 := by
      rw [smul_ne_zero_iff]
      exact ⟨hδ0, hx0⟩
    have hbT : (b : K) • T (δ • x0) = δ • x0 := by
      calc (b : K) • T (δ • x0) = (b : K) • ((σ δ) • T x0) := by rw [hsemi]
        _ = (σ δ) • ((b : K) • T x0) := by rw [smul_comm]
        _ = (σ δ) • (-x0) := by rw [hbTx0]
        _ = -(σ δ) • x0 := by rw [smul_neg, neg_smul]
        _ = -(-δ) • x0 := by rw [hδ]
        _ = δ • x0 := by rw [neg_neg]
    exact key (δ • x0) hvne hbT
  · refine key (x0 + normalizedOperator T b x0) hx ?_
    have h2 : (b : K) • T (normalizedOperator T b x0) = x0 := by
      simpa [normalizedOperator_apply] using hR x0
    rw [map_add, smul_add, show (b : K) • T x0 = normalizedOperator T b x0 from rfl, h2,
      add_comm]

theorem exists_fixed_pElement_statedProj_sp [Finite K] (hK : ringChar K ≠ 2) {r : ℕ}
    (hr : 2 ≤ r) (β : MulAut (StatedProj (StatedSp r K))) (hβ : β ^ 2 = 1) :
    ∃ u : StatedProj (StatedSp r K), u ≠ 1 ∧ u ^ ringChar K = 1 ∧ β u = u := by
  have hr1 : 1 ≤ r := by omega
  have hβ2 : β * β = 1 := by rw [← pow_two]; exact hβ
  have hB : (pairedSympForm K r).IsAlt := SymplecticFlag.pairedSympForm_isAlt
  have hnd : (pairedSympForm K r).Nondegenerate := SymplecticFlag.pairedSympForm_nondegenerate
  have hdim : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := SymplecticFlag.finrank_standard
  have hdim4 : 4 ≤ Module.finrank K (Fin r ⊕ Fin r → K) := by rw [hdim]; omega
  have : Nontrivial (Fin r ⊕ Fin r → K) := by
    refine ⟨fun _ => 1, fun _ => 0, ?_⟩
    intro h
    exact one_ne_zero (congrFun h (Sum.inl ⟨0, by omega⟩))
  let e := projectiveStatedEquiv (K := K) hr1
  have htrans : ∀ x : projectiveSymplectic (pairedSympForm K r), x ≠ 1 → x ^ ringChar K = 1 →
      e.symm x ≠ 1 ∧ (e.symm x) ^ ringChar K = 1 := by
    intro x hx hxp
    constructor
    · intro h
      apply hx
      have := congrArg e h
      simpa using this
    · apply e.injective
      rw [map_pow, e.apply_symm_apply, hxp, map_one]
  by_cases hβ1 : β = 1
  ·
    have hsq : ∀ x : Fin r ⊕ Fin r → K,
        (LinearEquiv.refl K (Fin r ⊕ Fin r → K))
          ((LinearEquiv.refl K (Fin r ⊕ Fin r → K)) x) = (1 : K) • x := by
      intro x; simp
    have hsim : ∀ x y : Fin r ⊕ Fin r → K,
        (pairedSympForm K r) ((LinearEquiv.refl K (Fin r ⊕ Fin r → K)) x)
          ((LinearEquiv.refl K (Fin r ⊕ Fin r → K)) y) = (1 : K) * (pairedSympForm K r) x y := by
      intro x y; simp
    obtain ⟨N, hN, hNN, hskew, -⟩ :=
      exists_sqZero_commute_similitude hK hdim4 (pairedSympForm K r) hB hnd
        (LinearEquiv.refl K _) 1 1 hsq hsim
    obtain ⟨U, -, hUne, hUp⟩ :=
      exists_isometry_one_add_sqZero hK (pairedSympForm K r) N hN hNN hskew
    have hxp : (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U) ^ ringChar K = 1 := by
      rw [← map_pow, hUp, map_one]
    obtain ⟨hx1, hxp'⟩ := htrans (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U)
      hUne hxp
    exact ⟨e.symm (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U), hx1, hxp',
      by rw [hβ1]; rfl⟩
  · obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, -, -⟩ :=
      (odd_symplectic_automorphism_semilinear_representation hK hr).2.2 β hβ2 hβ1
    set μ := multiplierUnit A with hμdef
    have hμ := multiplierUnit_spec A
    by_cases hσ : σ = 1
    ·
      subst hσ
      have hint : ∀ x, e (β x) = projectiveConjugation (pairedSympForm K r)
          (matrixLinIso (A : GL (Fin r ⊕ Fin r) K)) μ
          (matrix_similitude _ μ hμ) (e x) := by
        intro x
        rw [hα, map_one, mul_one]
        exact projectiveStatedEquiv_conjAut hr1 A μ hμ x
      have hsquare : ∀ x, matrixLinIso (A : GL (Fin r ⊕ Fin r) K)
          (matrixLinIso (A : GL (Fin r ⊕ Fin r) K) x) = (d : K) • x :=
        semilinearCoordMap_sq _ 1 hσ2 d hd
      obtain ⟨N, hN, hNN, hskew, hcomm⟩ :=
        exists_sqZero_commute_similitude hK hdim4 (pairedSympForm K r) hB hnd
          (matrixLinIso (A : GL (Fin r ⊕ Fin r) K)) d μ hsquare
          (matrix_similitude _ μ hμ)
      obtain ⟨U, hU, hUne, hUp⟩ :=
        exists_isometry_one_add_sqZero hK (pairedSympForm K r) N hN hNN hskew
      have hfix : similitudeConjugation (pairedSympForm K r)
          (matrixLinIso (A : GL (Fin r ⊕ Fin r) K)) μ
          (matrix_similitude _ μ hμ) U = U := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        rw [similitudeConjugation_apply, hU, map_add, LinearEquiv.apply_symm_apply,
          hcomm, LinearEquiv.apply_symm_apply, hU]
      have hproj : projectiveConjugation (pairedSympForm K r)
          (matrixLinIso (A : GL (Fin r ⊕ Fin r) K)) μ
          (matrix_similitude _ μ hμ) (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U) =
            QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U := by
        rw [projectiveConjugation_mk, hfix]
      have hxp : (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U) ^ ringChar K = 1 := by
        rw [← map_pow, hUp, map_one]
      obtain ⟨hx1, hxp'⟩ := htrans (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U)
        hUne hxp
      have hxu : β (e.symm (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U))
          = e.symm (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U) := by
        apply e.injective
        rw [hint]
        rw [show e (e.symm (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U))
            = QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U from e.apply_symm_apply _]
        exact hproj
      exact ⟨e.symm (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U), hx1, hxp', hxu⟩
    ·
      have hint : ∀ x, e (β x) = projectiveSemilinearConjugation (pairedSympForm K r) σ
          (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ
          (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ) (e x) := by
        intro x
        rw [hα]
        exact projectiveStatedEquiv_conjAut_fieldAut hr1 A σ μ hμ x
      obtain ⟨N, hN, hNN, hskew, hcomm⟩ :=
        exists_sqZero_commute_semilinear (pairedSympForm K r) hB hnd σ hσ2 hσ
          (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) d μ
          (semilinearCoordMap_smul _ σ)
          (semilinearCoordMap_sq _ σ hσ2 d hd)
          (semilinearCoordMap_form _ σ μ hμ)
      obtain ⟨U, hU, hUne, hUp⟩ :=
        exists_isometry_one_add_sqZero hK (pairedSympForm K r) N hN hNN hskew
      have hfix : semilinearConjugation (pairedSympForm K r) σ
          (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ
          (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ) U = U := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        rw [semilinearConjugation_apply, hU, map_add, hcomm, AddEquiv.apply_symm_apply, hU]
      have hproj : projectiveSemilinearConjugation (pairedSympForm K r) σ
          (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ
          (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ)
          (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U) =
            QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U := by
        rw [projectiveSemilinearConjugation_mk, hfix]
      have hxp : (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U) ^ ringChar K = 1 := by
        rw [← map_pow, hUp, map_one]
      obtain ⟨hx1, hxp'⟩ := htrans (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U)
        hUne hxp
      have hxu : β (e.symm (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U))
          = e.symm (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U) := by
        apply e.injective
        rw [hint]
        rw [show e (e.symm (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U))
            = QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U from e.apply_symm_apply _]
        exact hproj
      exact ⟨e.symm (QuotientGroup.mk' (scalarSigns (pairedSympForm K r)) U), hx1, hxp', hxu⟩

end CFSG.LocalAnalysis.WeakClosure81
