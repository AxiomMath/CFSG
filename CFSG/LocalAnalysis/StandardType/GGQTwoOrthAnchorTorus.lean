module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorus
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusNorm
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
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
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.OrthAnchor

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits Multiplicative
open CFSG.StandardType.OrthTorus

section Char

variable {K : Type} [Field K]

theorem zeta_ne_zero {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ≠ 0 := by
  rintro rfl
  simp at hζ

theorem zeta_pow_three {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ^ 3 = 1 := by
  have h : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by rw [hζ, mul_zero]
  have h' : (ζ - 1) * (ζ ^ 2 + ζ + 1) = ζ ^ 3 - 1 := by ring
  rw [h'] at h
  exact sub_eq_zero.mp h

private theorem oaC_zeta_ne_one [CharP K 2] {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ≠ 1 := by
  intro h
  rw [h] at hζ
  have hsum : (1 : K) + 1 + 1 = 0 := by simpa using hζ
  have h3 : (3 : K) = 0 := by
    rw [show (3 : K) = 1 + 1 + 1 by norm_num]
    exact hsum
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3' : (3 : K) = 1 := by
    rw [show (3 : K) = (2 : K) + 1 by norm_num, h2, zero_add]
  rw [h3'] at h3
  exact one_ne_zero h3

@[expose] noncomputable def zetaChar {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    Multiplicative (ZMod 3) →* Kˣ where
  toFun a := Units.mk0 (ζ ^ (toAdd a).val) (pow_ne_zero _ (zeta_ne_zero hζ))
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    let : NeZero 3 := ⟨by norm_num⟩
    apply Units.ext
    simp only [Units.val_mk0, Units.val_mul]
    rw [toAdd_mul, ZMod.val_add]
    rw [← pow_eq_pow_mod (a := ζ) (n := 3)
      (m := (toAdd a).val + (toAdd b).val) (zeta_pow_three hζ), pow_add]

theorem zetaChar_apply {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) (a : Multiplicative (ZMod 3)) :
    (zetaChar hζ a : K) = ζ ^ (toAdd a).val :=
  rfl

theorem zetaChar_injective [CharP K 2] {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    Function.Injective (zetaChar hζ) := by
  have hζ0 : ζ ≠ 0 := zeta_ne_zero hζ
  have hζ1 : ζ ≠ 1 := oaC_zeta_ne_one hζ
  have hζ3 : ζ ^ 3 = 1 := zeta_pow_three hζ
  let u : Kˣ := Units.mk0 ζ hζ0
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, hζ3]
  have hu1 : u ≠ 1 := by
    intro h
    apply hζ1
    have := congrArg Units.val h
    rwa [Units.val_mk0, Units.val_one] at this
  have hord : orderOf u = 3 := by
    have hdvd : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hu1
    · exact h3
  intro a b hab
  have hv : (toAdd a).val = (toAdd b).val := by
    have h' := congrArg Units.val hab
    rw [zetaChar_apply, zetaChar_apply] at h'
    have h'u : u ^ (toAdd a).val = u ^ (toAdd b).val := by
      apply Units.ext
      simpa [u] using h'
    have hmod := (pow_eq_pow_iff_modEq (x := u) (n := (toAdd a).val)
      (m := (toAdd b).val)).mp h'u
    rw [hord] at hmod
    exact hmod.eq_of_lt_of_lt (ZMod.val_lt (toAdd a)) (ZMod.val_lt (toAdd b))
  have h : toAdd a = toAdd b := ZMod.val_injective 3 hv
  simpa using congrArg ofAdd h

end Char

section Frame

variable {F K : Type} [Field F] [Field K] [Algebra F K]

private noncomputable def oaC_frame {m : ℕ} :
    ((Fin m → K) × (Fin 2 → F)) ≃ₗ[F] ((F × F) × (Fin m → K)) where
  toFun p := ((p.2 0, p.2 1), p.1)
  invFun v := (v.2, ![v.1.1, v.1.2])
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv p := by
    refine Prod.ext rfl ?_
    funext i
    fin_cases i <;> rfl
  right_inv v := by
    refine Prod.ext (Prod.ext ?_ ?_) rfl <;> simp

private theorem oaC_frame_apply {m : ℕ} (d : Fin m → K) (w : Fin 2 → F) :
    oaC_frame (F := F) (K := K) (m := m) (d, w) = ((w 0, w 1), d) := rfl

end Frame

section Torus

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
  (E : QuadExt F K (unitaryInvolution K 2 1))

include E in
theorem card_eq_two_of_quadExt : Nat.card F = 2 := by
  have hbool : ∀ a : F, a = 0 ∨ a = 1 := by
    intro a
    have h1 : (algebraMap F K a) ^ 2 = algebraMap F K a := by
      have h := E.fix a
      rw [unitaryInvolution_apply, show (2 : ℕ) ^ 1 = 2 by norm_num] at h
      exact h
    have h2 : algebraMap F K a * (algebraMap F K a - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_two, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · left
      exact (algebraMap F K).injective (by rw [h, map_zero])
    · right
      exact (algebraMap F K).injective (by rw [sub_eq_zero.mp h, map_one])
  have : Finite F := Finite.of_injective _ (algebraMap F K).injective
  rw [Nat.card_eq_two_iff' (0 : F)]
  exact ⟨1, one_ne_zero, fun y hy => (hbool y).resolve_left hy⟩

@[expose] noncomputable def zetaTorus {m : ℕ} (hm : 2 ≤ m) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (Fin m → Multiplicative (ZMod 3)) →* normOmega E m :=
  normPlaneTorus E hm (by norm_num) (zetaChar hζ)

theorem zetaTorus_apply {m : ℕ} (hm : 2 ≤ m) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0)
    (t : Fin m → Multiplicative (ZMod 3)) (v : (F × F) × (Fin m → K)) :
    ((zetaTorus E hm hζ t : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v =
      (v.1, fun i => ζ ^ (toAdd (t i)).val * v.2 i) := by
  unfold zetaTorus
  rw [normPlaneTorus_apply]
  refine Prod.ext rfl (funext fun i => ?_)
  simpa using congrArg (fun x : K => x * v.2 i) (zetaChar_apply hζ (t i))

theorem zetaTorus_injective {m : ℕ} (hm : 2 ≤ m) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    Function.Injective (zetaTorus E hm hζ) := by
  unfold zetaTorus
  exact normPlaneTorus_injective E hm (by norm_num) (zetaChar_injective hζ)

private theorem oaC_zetaTorus_coordTorus {m : ℕ} (hm : 2 ≤ m) {ζ : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) {cE : K ≃ₗ[F] K} (hcp : cE ^ 3 = 1)
    (hcE : ∀ x : K, cE x = ζ * x) (f : Fin m → Multiplicative (ZMod 3)) :
    coordTorus (a := id) (oaC_frame (F := F) (K := K) (m := m)) hcp f =
      (zetaTorus E hm hζ f :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) := by
  have hcEpow : ∀ (k : ℕ) (x : K), (cE ^ k) x = ζ ^ k * x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ, LinearEquiv.mul_apply, hcE, ih, pow_succ]
        ring
  apply LinearEquiv.ext
  intro v
  obtain ⟨⟨d, w⟩, rfl⟩ := (oaC_frame (F := F) (K := K) (m := m)).surjective v
  rw [coordTorus_apply (Φ := oaC_frame (F := F) (K := K) (m := m)) (hcp := hcp) (a := id)
    f d w]
  rw [zetaTorus_apply E hm hζ f]
  have harg : (fun i : Fin m =>
      (cE ^ (OmMv.extC id (fun j => toAdd (f j)) i).val) (d i)) =
      (fun i => ζ ^ (toAdd (f i)).val * d i) := by
    funext i
    have hext : OmMv.extC id (fun j => toAdd (f j)) i = toAdd (f i) :=
      OmMv.extC_apply_self (a := id) Function.injective_id (fun j => toAdd (f j)) i
    rw [hext]
    exact hcEpow _ _
  rw [harg]
  simp only [oaC_frame_apply]

theorem zetaTorus_normalizer {m : ℕ} (hm : 2 ≤ m) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0)
    (g : normOmega E m)
    (hg : ∀ f, ∃ f', g * zetaTorus E hm hζ f * g⁻¹ = zetaTorus E hm hζ f') :
    ∃ (π : Equiv.Perm (Fin m)) (ε : Fin m → ZMod 3), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f', g * zetaTorus E hm hζ f * g⁻¹ = zetaTorus E hm hζ f' →
        ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Finite F := Finite.of_injective _ (algebraMap F K).injective
  have hζ0 : ζ ≠ 0 := zeta_ne_zero hζ
  have hζ1 : ζ ≠ 1 := oaC_zeta_ne_one hζ
  have hζ3 : ζ ^ 3 = 1 := zeta_pow_three hζ
  let u : Kˣ := Units.mk0 ζ hζ0
  let cE : K ≃ₗ[F] K := Units.mulLeftLinearEquiv F K u
  have hcE : ∀ x : K, cE x = ζ * x := by
    intro x
    rw [show cE = Units.mulLeftLinearEquiv F K u from rfl]
    rw [Units.mulLeftLinearEquiv_apply, Units.val_mk0]
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, hζ3]
  have hcp : cE ^ 3 = 1 := by
    change (Units.mulLeftLinearEquiv F K u) ^ 3 = 1
    rw [← map_pow, hu3, map_one]
  have hfix : ∀ x : K, cE x = x → x = 0 := by
    intro x hx
    rw [hcE] at hx
    have h : (ζ - 1) * x = 0 := by linear_combination hx
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hζ1
    · exact h1
  have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  have hc1 : ∀ y : K, ∃ y₀ : K, cE y₀ - y₀ = y := by
    intro y
    refine ⟨(ζ - 1)⁻¹ * y, ?_⟩
    rw [hcE]
    calc ζ * ((ζ - 1)⁻¹ * y) - (ζ - 1)⁻¹ * y
        = (ζ - 1) * ((ζ - 1)⁻¹ * y) := by ring
      _ = y := by rw [← mul_assoc, mul_inv_cancel₀ hζ1', one_mul]
  have hroots : ∀ (e : ZMod 3) (θ : K →ₗ[F] K), Function.Injective θ →
      (∀ x, θ (cE x) = (cE ^ e.val) (θ x)) → e = 1 ∨ e = -1 := by
    let : Fact (1 < 3) := ⟨by norm_num⟩
    intro e θ hθ hθc
    have he : e = 0 ∨ e = 1 ∨ e = 2 := by
      have hcases : e.val = 0 ∨ e.val = 1 ∨ e.val = 2 := by
        have h0 : e.val < 3 := ZMod.val_lt e
        omega
      rcases hcases with h | h | h
      · left
        apply ZMod.val_injective 3
        rw [h, ZMod.val_zero]
      · right; left
        apply ZMod.val_injective 3
        rw [h, ZMod.val_one]
      · right; right
        apply ZMod.val_injective 3
        rw [h, ZMod.val_ofNat]
    rcases he with rfl | rfl | rfl
    · exfalso
      have h := hθc 1
      rw [ZMod.val_zero, pow_zero] at h
      have h1 : cE 1 = 1 := hθ (by simpa using h)
      exact hζ1 (by simpa [hcE] using h1)
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hcoord : ∀ f : Fin m → Multiplicative (ZMod 3),
      coordTorus (a := id) (oaC_frame (F := F) (K := K) (m := m)) hcp f =
        (zetaTorus E hm hζ f :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) :=
    fun f => oaC_zetaTorus_coordTorus (E := E) hm hζ hcp hcE f
  have hinj : Function.Injective
      (coordTorus (a := id) (oaC_frame (F := F) (K := K) (m := m)) hcp) := by
    intro f f' hff'
    apply zetaTorus_injective E hm hζ
    apply Subtype.ext
    rwa [← hcoord f, ← hcoord f']
  have hg' : ∀ f : Fin m → Multiplicative (ZMod 3),
      ∃ f', (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
          coordTorus (a := id) (oaC_frame (F := F) (K := K) (m := m)) hcp f *
          (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))⁻¹ =
        coordTorus (a := id) (oaC_frame (F := F) (K := K) (m := m)) hcp f' := by
    intro f
    obtain ⟨f', hf'⟩ := hg f
    refine ⟨f', ?_⟩
    have hval : (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
        (zetaTorus E hm hζ f :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
        (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))⁻¹ =
        (zetaTorus E hm hζ f' :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) := by
      have h := congrArg Subtype.val hf'
      simpa using h
    rw [hcoord f, hcoord f']
    exact hval
  obtain ⟨π, ε, hε, hmain⟩ := coordTorus_normalizer (K := F) (D := K)
    (oaC_frame (F := F) (K := K) (m := m)) hcp hfix hc1 Function.injective_id hinj hroots
    (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) hg'
  refine ⟨π, ε, hε, ?_⟩
  intro f f' hff' i
  refine hmain f f' ?_ i
  rw [hcoord f, hcoord f']
  simpa using congrArg Subtype.val hff'

theorem normOmegaConj_normBar_zetaTorus {m : ℕ} (hm : 2 ≤ m) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0)
    (S : Finset (Fin m)) (t : Fin m → Multiplicative (ZMod 3)) :
    normOmegaConj E (normBar_mem_orthogonalGroup E S) (zetaTorus E hm hζ t) =
      zetaTorus E hm hζ (fun i => if i ∈ S then (t i)⁻¹ else t i) := by
  unfold zetaTorus
  exact normOmegaConj_normBar_normPlaneTorus E hm (by norm_num) (zetaChar hζ) S t

end Torus

end CFSG.StandardType.OrthAnchor

end
