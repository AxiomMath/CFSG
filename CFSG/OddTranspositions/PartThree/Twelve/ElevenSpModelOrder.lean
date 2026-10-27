module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpModelChart
import CFSG.RankThree.PartOne.AUTSL.TraceASApply
import CFSG.ClassicalGroups.Orthogonal.CharTwoReflectGen
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpArith
import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
import CFSG.ClassicalInvolution.ModelFacts.MF15Sign
import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelRoot
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
import CFSG.ClassicalInvolution.ModelFacts.MF15Sq
import CFSG.ClassicalInvolution.Models.LinearPairs
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
import CFSG.LieType.CurtisTits.Symplectic
import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open QuadraticMap
open CFSG.Timmesfeld.Bridge CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
open CFSG.Open CFSG.OddTranspositions.PartFour CFSG.RankThree.PartOne.AUTSL
open CFSG.GroupTheory.WeirSylow
open CFSG.ComponentClassification.UnbalancedCatalog (polar_self_charTwo)

variable {k : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
  (hQ₀ : ∀ a b, QuadraticMap.polar Q₀ a b = spForm k F a b)

omit [Fintype F] [DecidableEq F] in
private lemma mRefl_mul_apply {Y : MSpace k F} (hY : mForm Q₀ Y = 1) (X : MSpace k F) :
    ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) X =
      X + polar (mForm Q₀) Y X • Y +
        (polar (mForm Q₀) mU X + Y.1.2 * polar (mForm Q₀) Y X) • mU := by
  change (mRefl Q₀ mU : MSpace k F ≃ₗ[F] MSpace k F)
    ((mRefl Q₀ Y : MSpace k F ≃ₗ[F] MSpace k F) X) = _
  rw [mRefl_apply_of_mForm_eq_one hY, mRefl_apply_of_mForm_eq_one mForm_mU,
    polar_add_right, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
    polar_mU_eq_snd Y]
  rw [show polar (mForm Q₀) mU X + polar (mForm Q₀) Y X * Y.1.2 =
      polar (mForm Q₀) mU X + Y.1.2 * polar (mForm Q₀) Y X from by ring]

omit [Fintype F] [DecidableEq F] in
private lemma mRefl_apply_mem_span {Y X x : MSpace k F} (hX : mForm Q₀ X = 1)
    (hXP : X ∈ Submodule.span F {mU, Y}) (hx : x ∈ Submodule.span F {mU, Y}) :
    (mRefl Q₀ X : MSpace k F ≃ₗ[F] MSpace k F) x ∈ Submodule.span F {mU, Y} := by
  rw [mRefl_apply_of_mForm_eq_one hX]
  exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ hXP)

omit [Fintype F] [DecidableEq F] in
private lemma mRefl_mul_apply_mem_span {Y : MSpace k F} (hY : mForm Q₀ Y = 1)
    {x : MSpace k F} (hx : x ∈ Submodule.span F {mU, Y}) :
    ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) x ∈
      Submodule.span F {mU, Y} := by
  change ((mRefl Q₀ mU : MSpace k F ≃ₗ[F] MSpace k F) *
    (mRefl Q₀ Y : MSpace k F ≃ₗ[F] MSpace k F)) x ∈ _
  rw [LinearEquiv.mul_apply]
  exact mRefl_apply_mem_span mForm_mU (Submodule.subset_span (by simp))
    (mRefl_apply_mem_span hY (Submodule.subset_span (by simp)) hx)

omit [Fintype F] [DecidableEq F] in
private lemma mRefl_mul_inv_apply_mem_span {Y : MSpace k F} (hY : mForm Q₀ Y = 1)
    {x : MSpace k F} (hx : x ∈ Submodule.span F {mU, Y}) :
    ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F)⁻¹ x ∈
      Submodule.span F {mU, Y} := by
  have hYX : Y ∈ Submodule.span F {mU, Y} := Submodule.subset_span (by simp)
  have hUX : mU ∈ Submodule.span F {mU, Y} := Submodule.subset_span (by simp)
  have hinv : ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) :
        MSpace k F ≃ₗ[F] MSpace k F)⁻¹ =
      (mRefl Q₀ Y : MSpace k F ≃ₗ[F] MSpace k F) *
        (mRefl Q₀ mU : MSpace k F ≃ₗ[F] MSpace k F) := by
    change ((CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) mU) *
      (CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) Y))⁻¹ = _
    rw [mul_inv_rev,
      inv_eq_of_mul_eq_one_left
        (CFSG.ClassicalGroups.Orthogonal.reflect_mul_self (mForm Q₀) Y),
      inv_eq_of_mul_eq_one_left
        (CFSG.ClassicalGroups.Orthogonal.reflect_mul_self (mForm Q₀) mU)]
    rfl
  rw [hinv, LinearEquiv.mul_apply]
  exact mRefl_apply_mem_span hY hYX (mRefl_apply_mem_span mForm_mU hUX hx)

omit [Fintype F] [DecidableEq F] in
private lemma mRefl_mul_mem_stabSub {Y : MSpace k F} (hY : mForm Q₀ Y = 1) :
    ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ∈
      CFSG.ClassicalGroups.Orthogonal.Small.stabSub (Submodule.span F {mU, Y}) := by
  intro x
  constructor
  · exact mRefl_mul_apply_mem_span hY
  · intro hx
    have hinv := mRefl_mul_inv_apply_mem_span hY hx
    simpa using hinv

omit [Fintype F] [DecidableEq F] in
private lemma exists_mem_span_mU_Y_add_polar_eq_zero {Y : MSpace k F}
    (hβ : Y.1.2 ≠ 0) (x : MSpace k F) :
    ∃ p ∈ Submodule.span F {mU, Y}, ∃ w : MSpace k F,
      polar (mForm Q₀) mU w = 0 ∧ polar (mForm Q₀) Y w = 0 ∧ p + w = x := by
  have hYX : Y ∈ Submodule.span F {mU, Y} := Submodule.subset_span (by simp)
  have hUX : mU ∈ Submodule.span F {mU, Y} := Submodule.subset_span (by simp)
  have hUU : polar (mForm Q₀) mU mU = 0 :=
    polar_self_charTwo (mForm Q₀) mU
  have hYY : polar (mForm Q₀) Y Y = 0 :=
    polar_self_charTwo (mForm Q₀) Y
  have hUY : polar (mForm Q₀) mU Y = Y.1.2 := polar_mU_eq_snd Y
  have hYU : polar (mForm Q₀) Y mU = Y.1.2 := by
    rw [polar_comm (mForm Q₀) Y mU]
    exact hUY
  refine ⟨(polar (mForm Q₀) x Y / Y.1.2) • mU + (polar (mForm Q₀) x mU / Y.1.2) • Y, ?_,
    x - ((polar (mForm Q₀) x Y / Y.1.2) • mU + (polar (mForm Q₀) x mU / Y.1.2) • Y), ?_, ?_,
    by abel⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ hUX) (Submodule.smul_mem _ _ hYX)
  · rw [polar_sub_right, polar_add_right, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hUU, hUY, mul_zero, zero_add,
      polar_comm (mForm Q₀) x mU, div_mul_cancel₀ _ hβ, sub_self]
  · rw [polar_sub_right, polar_add_right, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hYU, hYY, mul_zero, add_zero,
      polar_comm (mForm Q₀) x Y, div_mul_cancel₀ _ hβ, sub_self]

omit [Fintype F] [DecidableEq F] in
private lemma mRefl_mul_apply_eq_self_of_polar_eq_zero {Y : MSpace k F}
    (hY : mForm Q₀ Y = 1) {w : MSpace k F} (hUw : polar (mForm Q₀) mU w = 0)
    (hYw : polar (mForm Q₀) Y w = 0) :
    ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) w = w := by
  rw [mRefl_mul_apply hY, hUw, hYw, mul_zero, add_zero, zero_smul]
  module

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma pow_apply_eq_self_of_apply_eq_self {g : MSpace k F ≃ₗ[F] MSpace k F}
    {w : MSpace k F} (hw : g w = w) (m : ℕ) : (g ^ m) w = w := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hw]

omit [DecidableEq F] in
private lemma exists_sq_add_mul_add_one_eq_zero_of_mem_artinSchreier {Y : MSpace k F}
    (hβ : Y.1.2 ≠ 0)
    (hAS : (Y.1.2)⁻¹ ∈ (artinSchreierHom (K := F)).range) :
    ∃ u : F, u ^ 2 + Y.1.2 * u + 1 = 0 := by
  have hsq : (Y.1.2)⁻¹ ^ 2 ∈ (artinSchreierHom (K := F)).range :=
    (sq_mem_range_artinSchreier_iff (Y.1.2)⁻¹).mpr hAS
  obtain ⟨w, hw⟩ := hsq
  rw [artinSchreierHom_apply, ← pow_two] at hw
  refine ⟨Y.1.2 * w, ?_⟩
  have h1 : Y.1.2 ^ 2 * (w ^ 2 + w) = 1 := by
    rw [hw, ← mul_pow, mul_inv_cancel₀ hβ, one_pow]
  calc (Y.1.2 * w) ^ 2 + Y.1.2 * (Y.1.2 * w) + 1
      = Y.1.2 ^ 2 * (w ^ 2 + w) + 1 := by ring
    _ = 1 + 1 := by rw [h1]
    _ = 0 := CharTwo.add_self_eq_zero 1

omit [Fintype F] [DecidableEq F] in
private lemma mForm_smul_mU_add {Y : MSpace k F} (hY : mForm Q₀ Y = 1) (s t : F) :
    mForm Q₀ (s • mU + t • Y) = s ^ 2 + s * t * Y.1.2 + t ^ 2 := by
  rw [QuadraticMap.map_add (mForm Q₀), CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq,
    CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, mForm_mU, hY,
    CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
    CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, polar_mU_eq_snd Y]
  ring

omit [Fintype F] [DecidableEq F] in
private lemma polar_smul_mU_add_smul {Y : MSpace k F}
    (s t s' t' : F) :
    polar (mForm Q₀) (s • mU + t • Y) (s' • mU + t' • Y) =
      Y.1.2 * (s * t' + t * s') := by
  rw [polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
    CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, polar_add_right, polar_add_right,
    CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
    CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
    CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
    CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
    polar_self_charTwo (mForm Q₀) mU,
    polar_self_charTwo (mForm Q₀) Y,
    polar_mU_eq_snd Y,
    polar_comm (mForm Q₀) Y mU, polar_mU_eq_snd Y]
  ring

omit [Fintype F] [DecidableEq F] in
private lemma mForm_smul_mU_add_one_of_sq_add_mul_add_one {Y : MSpace k F}
    (hY : mForm Q₀ Y = 1) {u : F} (hu : u ^ 2 + Y.1.2 * u + 1 = 0) :
    mForm Q₀ (u • mU + Y) = 0 := by
  have h := mForm_smul_mU_add hY u 1
  rw [one_smul] at h
  rw [h]
  linear_combination hu

omit [Fintype F] [DecidableEq F] in
private lemma mForm_add_smul_mU_add_one_of_sq_add_mul_add_one {Y : MSpace k F}
    (hY : mForm Q₀ Y = 1) {u : F} (hu : u ^ 2 + Y.1.2 * u + 1 = 0) :
    mForm Q₀ ((Y.1.2 + u) • mU + Y) = 0 := by
  have h := mForm_smul_mU_add hY (Y.1.2 + u) 1
  rw [one_smul] at h
  rw [h]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination hu + (Y.1.2 ^ 2 + Y.1.2 * u) * h2

omit [Fintype F] [DecidableEq F] in
private lemma polar_smul_mU_add_one_smul_mU_add_one {Y : MSpace k F} {u : F} :
    polar (mForm Q₀) (u • mU + Y) ((Y.1.2 + u) • mU + Y) = Y.1.2 ^ 2 := by
  have h := polar_smul_mU_add_smul (Q₀ := Q₀) (Y := Y) u 1 (Y.1.2 + u) 1
  rw [one_smul] at h
  rw [h]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (Y.1.2 * u) * h2

omit [Fintype F] [DecidableEq F] in
private lemma mRefl_mul_apply_smul_mU_add_one {Y : MSpace k F} (hY : mForm Q₀ Y = 1)
    {u : F} (hu : u ^ 2 + Y.1.2 * u + 1 = 0) :
    ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F)
        (u • mU + Y) = (1 + u * Y.1.2) • (u • mU + Y) := by
  rw [mRefl_mul_apply hY]
  have hYv : polar (mForm Q₀) Y (u • mU + Y) = u * Y.1.2 := by
    rw [polar_add_right, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
      polar_self_charTwo (mForm Q₀) Y,
      polar_comm (mForm Q₀) Y mU,
      polar_mU_eq_snd Y]
    ring
  have hUv : polar (mForm Q₀) mU (u • mU + Y) = Y.1.2 := by
    rw [polar_add_right, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
      polar_self_charTwo (mForm Q₀) mU,
      polar_mU_eq_snd Y]
    ring
  rw [hYv, hUv]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hscal : u + (Y.1.2 + Y.1.2 * (u * Y.1.2)) = (1 + u * Y.1.2) * u := by
    linear_combination Y.1.2 * hu - (u ^ 2 * Y.1.2) * h2
  rw [smul_add, smul_smul, ← hscal]
  module

omit [Fintype F] [DecidableEq F] in
private lemma mRefl_mul_apply_add_smul_mU_add_one {Y : MSpace k F} (hY : mForm Q₀ Y = 1)
    {u : F} (hu : u ^ 2 + Y.1.2 * u + 1 = 0) :
    ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F)
        ((Y.1.2 + u) • mU + Y) =
      (1 + Y.1.2 ^ 2 + u * Y.1.2) • ((Y.1.2 + u) • mU + Y) := by
  rw [mRefl_mul_apply hY]
  have hYv : polar (mForm Q₀) Y ((Y.1.2 + u) • mU + Y) = (Y.1.2 + u) * Y.1.2 := by
    rw [polar_add_right, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
      polar_self_charTwo (mForm Q₀) Y,
      polar_comm (mForm Q₀) Y mU,
      polar_mU_eq_snd Y]
    ring
  have hUv : polar (mForm Q₀) mU ((Y.1.2 + u) • mU + Y) = Y.1.2 := by
    rw [polar_add_right, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
      polar_self_charTwo (mForm Q₀) mU,
      polar_mU_eq_snd Y]
    ring
  rw [hYv, hUv]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hscal : (Y.1.2 + u) + (Y.1.2 + Y.1.2 * ((Y.1.2 + u) * Y.1.2)) =
      (1 + Y.1.2 ^ 2 + u * Y.1.2) * (Y.1.2 + u) := by
    linear_combination Y.1.2 * hu - (u * Y.1.2 ^ 2 + u ^ 2 * Y.1.2) * h2
  rw [smul_add, smul_smul, ← hscal]
  module

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma pow_apply_eq_smul_of_apply_eq_smul {g : MSpace k F ≃ₗ[F] MSpace k F}
    {x : MSpace k F} {lam : F} (hx : g x = lam • x) (m : ℕ) :
    (g ^ m) x = lam ^ m • x := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero, one_smul]
    rfl
  | succ m ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]

omit [DecidableEq F] [CharP F 2] in
private lemma pow_apply_eq_self_of_apply_eq_smul {g : MSpace k F ≃ₗ[F] MSpace k F}
    {x : MSpace k F} {lam : F} (hx : g x = lam • x) (hlam : lam ≠ 0) :
    (g ^ (Fintype.card F - 1)) x = x := by
  rw [pow_apply_eq_smul_of_apply_eq_smul hx, FiniteField.pow_card_sub_one_eq_one lam hlam,
    one_smul]

omit [Fintype F] [DecidableEq F] in
private lemma finrank_span_mU_Y (Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)) {Y : MSpace k F}
    (hβ : Y.1.2 ≠ 0) :
    Module.finrank F (Submodule.span F {mU, Y}) = 2 := by
  have h₁ : polar (mForm Q₀) mU Y ≠ 0 := by
    rw [polar_mU_eq_snd Y]
    exact hβ
  have h₂ : polar (mForm Q₀) Y Y = 0 :=
    polar_self_charTwo (mForm Q₀) Y
  have h₃ : polar (mForm Q₀) Y mU ≠ 0 := by
    rw [polar_comm (mForm Q₀) Y mU, polar_mU_eq_snd Y]
    exact hβ
  exact CFSG.ClassicalInvolution.ModelFacts.MF15.finrank_span_pair_two
    (CFSG.ClassicalGroups.Orthogonal.OmegaSiegel.linearIndependent_pair_of_polar h₁ h₂ h₃)

omit [Fintype F] [DecidableEq F] in
private lemma span_smul_mU_add_one_eq_span {Y : MSpace k F} (hY : mForm Q₀ Y = 1)
    (hβ : Y.1.2 ≠ 0) {u : F} (hu : u ^ 2 + Y.1.2 * u + 1 = 0) :
    Submodule.span F {u • mU + Y, (Y.1.2 + u) • mU + Y} = Submodule.span F {mU, Y} := by
  have hYX : Y ∈ Submodule.span F {mU, Y} := Submodule.subset_span (by simp)
  have hUX : mU ∈ Submodule.span F {mU, Y} := Submodule.subset_span (by simp)
  have heP : u • mU + Y ∈ Submodule.span F {mU, Y} :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hUX) hYX
  have hfP : (Y.1.2 + u) • mU + Y ∈ Submodule.span F {mU, Y} :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hUX) hYX
  have hle : Submodule.span F {u • mU + Y, (Y.1.2 + u) • mU + Y} ≤
      Submodule.span F {mU, Y} := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact heP
    · exact hfP
  have hQe := mForm_smul_mU_add_one_of_sq_add_mul_add_one hY hu
  have hQf := mForm_add_smul_mU_add_one_of_sq_add_mul_add_one hY hu
  have hpol : polar (mForm Q₀) (u • mU + Y) ((Y.1.2 + u) • mU + Y) = Y.1.2 ^ 2 :=
    polar_smul_mU_add_one_smul_mU_add_one
  have hβ2 : Y.1.2 ^ 2 ≠ 0 := pow_ne_zero 2 hβ
  have hdim : Module.finrank F
      (Submodule.span F {u • mU + Y, (Y.1.2 + u) • mU + Y}) = 2 := by
    have hind : LinearIndependent F ![u • mU + Y, (Y.1.2 + u) • mU + Y] := by
      rw [LinearIndependent.pair_iff]
      intro a c hac
      have h1 := congrArg (fun z => polar (mForm Q₀) (u • mU + Y) z) hac
      have h2 := congrArg (fun z => polar (mForm Q₀) ((Y.1.2 + u) • mU + Y) z) hac
      rw [polar_add_right,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hQe, hpol, mul_zero, zero_add,
        polar_zero_right] at h1
      rw [polar_add_right,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, polar_comm (mForm Q₀),
        hpol, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hQf, mul_zero, add_zero,
        polar_zero_right] at h2
      exact ⟨(mul_eq_zero.mp h2).resolve_right hβ2, (mul_eq_zero.mp h1).resolve_right hβ2⟩
    have h5 := finrank_span_eq_card hind
    have hr : Set.range ![u • mU + Y, (Y.1.2 + u) • mU + Y] =
        {u • mU + Y, (Y.1.2 + u) • mU + Y} := by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
      simp [eq_comm]
    rw [hr] at h5
    simpa using h5
  exact Submodule.eq_of_le_of_finrank_eq hle
    (by rw [hdim, finrank_span_mU_Y Q₀ hβ])

omit [Fintype F] [DecidableEq F] in
private lemma resHom_pow_eq_one_of_span_eq {Y : MSpace k F} (hY : mForm Q₀ Y = 1)
    {e f : MSpace k F}
    (hspan : Submodule.span F {e, f} = Submodule.span F {mU, Y}) {n : ℕ}
    (he : (((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) :
      MSpace k F ≃ₗ[F] MSpace k F) ^ n) e = e)
    (hf : (((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) :
      MSpace k F ≃ₗ[F] MSpace k F) ^ n) f = f) :
    CFSG.ClassicalGroups.Orthogonal.Small.resHom (Submodule.span F {mU, Y})
      ⟨((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F),
        mRefl_mul_mem_stabSub hY⟩ ^ n = 1 := by
  refine LinearEquiv.ext fun p => Subtype.ext ?_
  have h1 : (((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) :
      MSpace k F ≃ₗ[F] MSpace k F) ^ n) (p : MSpace k F) = (p : MSpace k F) := by
    have hp : (p : MSpace k F) ∈ Submodule.span F {e, f} := by
      rw [hspan]
      exact p.2
    obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.mp hp
    rw [← hac, map_add, map_smul, map_smul, he, hf]
  rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_pow_apply]
  exact h1

omit [Fintype F] [DecidableEq F] in
private lemma pow_eq_one_of_pow_resHom_eq_one {Y : MSpace k F} (hY : mForm Q₀ Y = 1)
    (hβ : Y.1.2 ≠ 0) {n : ℕ}
    (h : CFSG.ClassicalGroups.Orthogonal.Small.resHom (Submodule.span F {mU, Y})
      ⟨((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F),
        mRefl_mul_mem_stabSub hY⟩ ^ n = 1) :
    ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ^ n = 1 := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨p, hp, w, hUw, hYw, hx⟩ :=
    exists_mem_span_mU_Y_add_polar_eq_zero hβ x
  rw [← hx, map_add]
  have hpp : (((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) :
      MSpace k F ≃ₗ[F] MSpace k F) ^ n) p = p := by
    have h1 := CFSG.ClassicalGroups.Orthogonal.Small.resHom_pow_apply
      (W := Submodule.span F {mU, Y})
      (ν := ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F))
      (mRefl_mul_mem_stabSub hY) n ⟨p, hp⟩
    rw [h] at h1
    simpa using h1.symm
  have hww : (((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) :
      MSpace k F ≃ₗ[F] MSpace k F) ^ n) w = w :=
    pow_apply_eq_self_of_apply_eq_self
      (mRefl_mul_apply_eq_self_of_polar_eq_zero hY hUw hYw) n
  rw [hpp, hww]
  rfl

omit [DecidableEq F] in
private lemma orderOf_mRefl_mul_dvd_card_sub_one_of_sq_add_mul_add_one {Y : MSpace k F}
    (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0) {u : F}
    (hu : u ^ 2 + Y.1.2 * u + 1 = 0) :
    orderOf (mRefl Q₀ mU * mRefl Q₀ Y) ∣ Fintype.card F - 1 := by
  have hUe : polar (mForm Q₀) mU (u • mU + Y) = Y.1.2 := by
    rw [polar_add_right, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
      polar_self_charTwo (mForm Q₀) mU,
      polar_mU_eq_snd Y]
    ring
  have he0 : u • mU + Y ≠ 0 := by
    intro h
    rw [h, polar_zero_right] at hUe
    exact hβ hUe.symm
  have hpol : polar (mForm Q₀) (u • mU + Y) ((Y.1.2 + u) • mU + Y) = Y.1.2 ^ 2 :=
    polar_smul_mU_add_one_smul_mU_add_one
  have hf0 : (Y.1.2 + u) • mU + Y ≠ 0 := by
    intro h
    rw [h, polar_zero_right] at hpol
    exact pow_ne_zero 2 hβ hpol.symm
  have hge := mRefl_mul_apply_smul_mU_add_one hY hu
  have hgf := mRefl_mul_apply_add_smul_mU_add_one hY hu
  have hlam : (1 + u * Y.1.2) ≠ 0 := by
    intro h
    have h0 : ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) :
        MSpace k F ≃ₗ[F] MSpace k F) (u • mU + Y) = 0 := by rw [hge, h, zero_smul]
    exact he0 (LinearEquiv.map_eq_zero_iff _ |>.mp h0)
  have hmu : (1 + Y.1.2 ^ 2 + u * Y.1.2) ≠ 0 := by
    intro h
    have h0 : ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) :
        MSpace k F ≃ₗ[F] MSpace k F) ((Y.1.2 + u) • mU + Y) = 0 := by
      rw [hgf, h, zero_smul]
    exact hf0 (LinearEquiv.map_eq_zero_iff _ |>.mp h0)
  have he := pow_apply_eq_self_of_apply_eq_smul hge hlam
  have hf := pow_apply_eq_self_of_apply_eq_smul hgf hmu
  have hspan := span_smul_mU_add_one_eq_span hY hβ hu
  have hres := resHom_pow_eq_one_of_span_eq hY hspan he hf
  have hpow := pow_eq_one_of_pow_resHom_eq_one hY hβ hres
  rw [orderOf_dvd_iff_pow_eq_one]
  exact Subtype.ext hpow

omit [DecidableEq F] in
private lemma odd_card_sub_one : Odd (Fintype.card F - 1) := by
  have h : Fintype.card F % 2 = 0 := FiniteField.even_card_of_char_two (ringChar.eq F 2)
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  exact ⟨m - 1, by omega⟩

omit [DecidableEq F] in
private lemma eq_zero_of_mForm_eq_zero_of_mem_span_mU_Y {Y : MSpace k F}
    (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0)
    (hAS : (Y.1.2)⁻¹ ∉ (artinSchreierHom (K := F)).range) {x : MSpace k F}
    (hxP : x ∈ Submodule.span F {mU, Y}) (hx : mForm Q₀ x = 0) : x = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hxP
  rw [mForm_smul_mU_add hY] at hx
  by_cases ht : t = 0
  · rw [ht] at hx
    simp only [mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero] at hx
    rw [ht, sq_eq_zero_iff.mp hx]
    simp
  · exfalso
    have htb : t * Y.1.2 ≠ 0 := mul_ne_zero ht hβ
    have hmem : ((Y.1.2)⁻¹) ^ 2 ∈ (artinSchreierHom (K := F)).range := by
      refine ⟨s / (t * Y.1.2), ?_⟩
      rw [artinSchreierHom_apply, ← pow_two]
      field_simp
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination hx - (t ^ 2) * h2
    exact hAS ((sq_mem_range_artinSchreier_iff (Y.1.2)⁻¹).mp hmem)

omit [DecidableEq F] in
private lemma orderOf_mRefl_mul_dvd_card_add_one_of_notMem_artinSchreier {Y : MSpace k F}
    (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0)
    (hAS : (Y.1.2)⁻¹ ∉ (artinSchreierHom (K := F)).range) :
    orderOf (mRefl Q₀ mU * mRefl Q₀ Y) ∣ 2 * (Fintype.card F + 1) := by
  have hdim : Module.finrank F (Submodule.span F {mU, Y}) = 2 :=
    finrank_span_mU_Y Q₀ hβ
  have hani : ∀ x : Submodule.span F {mU, Y}, x ≠ 0 →
      ((mForm Q₀).comp (Submodule.span F {mU, Y}).subtype) x ≠ 0 := by
    intro x hx hx0
    exact hx (Subtype.ext (eq_zero_of_mForm_eq_zero_of_mem_span_mU_Y hY hβ hAS
      x.property hx0))
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_of_anisotropic
    (K := F) (A := Submodule.span F {mU, Y})
    (Q := (mForm Q₀).comp (Submodule.span F {mU, Y}).subtype)
    hdim hani
  rw [Nat.card_eq_fintype_card (α := F)] at hcard
  have hmem := CFSG.ClassicalGroups.Orthogonal.Small.resHom_mem_orthogonalGroup
    (Q := mForm Q₀) (W := Submodule.span F {mU, Y})
    (c := ((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F))
    (mRefl Q₀ mU * mRefl Q₀ Y).2 (mRefl_mul_mem_stabSub hY)
  have hdvd : orderOf (CFSG.ClassicalGroups.Orthogonal.Small.resHom
      (Submodule.span F {mU, Y})
      ⟨((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F),
        mRefl_mul_mem_stabSub hY⟩) ∣ 2 * (Fintype.card F + 1) := by
    have h1 := Subgroup.orderOf_dvd_natCard
      (TauCeti.QuadraticMap.orthogonalGroup
        ((mForm Q₀).comp (Submodule.span F {mU, Y}).subtype)) hmem
    rwa [hcard] at h1
  have hres : CFSG.ClassicalGroups.Orthogonal.Small.resHom (Submodule.span F {mU, Y})
      ⟨((mRefl Q₀ mU * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F),
        mRefl_mul_mem_stabSub hY⟩ ^ (2 * (Fintype.card F + 1)) = 1 :=
    (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have hpow := pow_eq_one_of_pow_resHom_eq_one hY hβ hres
  rw [orderOf_dvd_iff_pow_eq_one]
  exact Subtype.ext hpow

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private lemma mRefl_mul_ne_one {Y : MSpace k F} (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0) :
    mRefl Q₀ mU * mRefl Q₀ Y ≠ 1 := by
  intro h
  have hsq : mRefl Q₀ mU * mRefl Q₀ mU = 1 :=
    Subtype.ext (CFSG.ClassicalGroups.Orthogonal.reflect_mul_self (mForm Q₀) mU)
  have h3 : mRefl Q₀ Y = mRefl Q₀ mU := by
    calc mRefl Q₀ Y = 1 * mRefl Q₀ Y := (one_mul _).symm
      _ = (mRefl Q₀ mU * mRefl Q₀ mU) * mRefl Q₀ Y := by rw [hsq]
      _ = mRefl Q₀ mU * (mRefl Q₀ mU * mRefl Q₀ Y) := by group
      _ = mRefl Q₀ mU * 1 := by rw [h]
      _ = mRefl Q₀ mU := mul_one _
  have hQ : (polarBilin (mForm Q₀)).Nondegenerate :=
    nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)
  have h4 : Y = mU :=
    (CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflect_iff hQ hY mForm_mU).mp
      (congrArg Subtype.val h3)
  have h5 : Y.1.2 = 0 := by rw [h4]; simp [mU]
  exact hβ h5

include hQ₀ in
theorem orderOf_mRefl_mul_dvd_iff {Y : MSpace k F} (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0) :
    orderOf (mRefl Q₀ mU * mRefl Q₀ Y) ∣ Fintype.card F - 1 ↔
      (Y.1.2)⁻¹ ∈ (artinSchreierHom (K := F)).range := by
  constructor
  · intro hdvd
    by_contra hAS
    have h2 := orderOf_mRefl_mul_dvd_card_add_one_of_notMem_artinSchreier hY hβ hAS
    have hcop : Nat.Coprime (2 * (Fintype.card F + 1)) (Fintype.card F - 1) := by
      have hodd := odd_card_sub_one (F := F)
      have htwo : Nat.Coprime 2 (Fintype.card F - 1) := Nat.coprime_two_left.mpr hodd
      have hq : Nat.Coprime (Fintype.card F + 1) (Fintype.card F - 1) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        have hq1 : 1 ≤ Fintype.card F := by
          have := Fintype.one_lt_card (α := F)
          omega
        rw [show Fintype.card F + 1 = 2 + (Fintype.card F - 1) by omega,
          Nat.gcd_add_self_left, htwo.gcd_eq_one]
      exact htwo.mul_left hq
    have hdvdgcd : orderOf (mRefl Q₀ mU * mRefl Q₀ Y) ∣
        Nat.gcd (2 * (Fintype.card F + 1)) (Fintype.card F - 1) := Nat.dvd_gcd h2 hdvd
    rw [hcop.gcd_eq_one] at hdvdgcd
    exact mRefl_mul_ne_one (hQ₀ := hQ₀) hY hβ
      (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvdgcd))
  · intro hAS
    obtain ⟨u, hu⟩ := exists_sq_add_mul_add_one_eq_zero_of_mem_artinSchreier hβ hAS
    exact orderOf_mRefl_mul_dvd_card_sub_one_of_sq_add_mul_add_one hY hβ hu

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
private lemma mStabForm_add_mStabForm (Y Y' : MSpace k F) (x : Fin k ⊕ Fin k → F) :
    mStabForm Q₀ Y x + mStabForm Q₀ Y' x =
      spForm k F ((Y.1.2)⁻¹ • Y.2 + (Y'.1.2)⁻¹ • Y'.2) x ^ 2 := by
  rw [mStabForm_apply (hQ₀ := hQ₀) Y, mStabForm_apply (hQ₀ := hQ₀) Y', map_add,
    LinearMap.add_apply, add_pow_char]
  have hQ : Q₀ x + Q₀ x = 0 := CharTwo.add_self_eq_zero (Q₀ x)
  calc Q₀ x + spForm k F ((Y.1.2)⁻¹ • Y.2) x ^ 2 +
        (Q₀ x + spForm k F ((Y'.1.2)⁻¹ • Y'.2) x ^ 2)
      = (Q₀ x + Q₀ x) + (spForm k F ((Y.1.2)⁻¹ • Y.2) x ^ 2 +
        spForm k F ((Y'.1.2)⁻¹ • Y'.2) x ^ 2) := by abel
    _ = spForm k F ((Y.1.2)⁻¹ • Y.2) x ^ 2 +
        spForm k F ((Y'.1.2)⁻¹ • Y'.2) x ^ 2 := by rw [hQ, zero_add]

include hQ₀ in
omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma mStabForm_smul (Y : MSpace k F) (c : F) (x : Fin k ⊕ Fin k → F) :
    mStabForm Q₀ Y (c • x) = c ^ 2 * mStabForm Q₀ Y x := by
  rw [mStabForm_apply (hQ₀ := hQ₀) Y, mStabForm_apply (hQ₀ := hQ₀) Y,
    QuadraticMap.map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_pow]
  ring

include hQ₀ in
private lemma exists_mStabForm_ne_zero_of_polar_eq_zero (hk : 2 ≤ k) (Y Y' : MSpace k F) :
    ∃ x : Fin k ⊕ Fin k → F,
      spForm k F ((Y.1.2)⁻¹ • Y.2 + (Y'.1.2)⁻¹ • Y'.2) x = 0 ∧
        mStabForm Q₀ Y x ≠ 0 := by
  by_contra h
  push Not at h
  set w : Fin k ⊕ Fin k → F := (Y.1.2)⁻¹ • Y.2 + (Y'.1.2)⁻¹ • Y'.2 with hw
  have hdimW : Module.finrank F (Fin k ⊕ Fin k → F) = 2 * k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hker : 2 * k - 1 ≤ Module.finrank F (LinearMap.ker (spForm k F w)) := by
    have h := LinearMap.finrank_range_add_finrank_ker (spForm k F w)
    have hle : Module.finrank F (LinearMap.range (spForm k F w)) ≤ 1 := by
      have h1 : Module.finrank F (LinearMap.range (spForm k F w)) ≤
          Module.finrank F (⊤ : Submodule F F) :=
        Submodule.finrank_mono (le_top : LinearMap.range (spForm k F w) ≤ ⊤)
      simpa using h1
    omega
  have hH : LinearMap.ker (spForm k F w) ≤
      (spForm k F).orthogonal (LinearMap.ker (spForm k F w)) := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have hxy : y + x ∈ LinearMap.ker (spForm k F w) := by
      rw [LinearMap.mem_ker, map_add, LinearMap.mem_ker.mp hx, LinearMap.mem_ker.mp hy,
        add_zero]
    have h0 : polar (mStabForm Q₀ Y) y x = 0 := by
      rw [QuadraticMap.polar, h y hy, h x hx, h (y + x) hxy]
      ring
    rw [← polar_mStabForm (hQ₀ := hQ₀) Y y x]
    exact h0
  have hle : Module.finrank F (LinearMap.ker (spForm k F w)) ≤
      Module.finrank F ((spForm k F).orthogonal (LinearMap.ker (spForm k F w))) :=
    Submodule.finrank_mono hH
  rw [LinearMap.BilinForm.finrank_orthogonal (spForm_nondegenerate (r := k))] at hle
  have hk' : 2 ≤ k := hk
  omega

include hQ₀ in
theorem exists_mStabForm_eq_one_of_two (hk : 2 ≤ k) (Y Y' : MSpace k F) :
    ∃ x : Fin k ⊕ Fin k → F, x ≠ 0 ∧ mStabForm Q₀ Y x = 1 ∧ mStabForm Q₀ Y' x = 1 := by
  obtain ⟨x, hxH, hx0⟩ := exists_mStabForm_ne_zero_of_polar_eq_zero (hQ₀ := hQ₀) hk Y Y'
  obtain ⟨c, hc⟩ := (frobeniusEquiv F 2).surjective (mStabForm Q₀ Y x)
  have hc' : c ^ 2 = mStabForm Q₀ Y x := by
    rw [← hc, frobeniusEquiv_def]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 2 ≠ 0)] at hc'
    exact hx0 hc'.symm
  have hxeq : mStabForm Q₀ Y x = mStabForm Q₀ Y' x := by
    refine CharTwo.add_eq_zero.mp ?_
    rw [mStabForm_add_mStabForm (hQ₀ := hQ₀) Y Y' x, hxH, zero_pow (by norm_num : 2 ≠ 0)]
  have hsq : ((c⁻¹) ^ 2) * mStabForm Q₀ Y x = 1 := by
    rw [← hc', ← mul_pow, inv_mul_cancel₀ hc0, one_pow]
  have hxne : x ≠ 0 := by
    intro h0
    exact hx0 (by rw [h0, mStabForm_apply (hQ₀ := hQ₀) Y]; simp)
  refine ⟨c⁻¹ • x, ?_, ?_, ?_⟩
  · intro h0
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact inv_ne_zero hc0 h1
    · exact hxne h1
  · rw [mStabForm_smul (hQ₀ := hQ₀) Y, hsq]
  · rw [mStabForm_smul (hQ₀ := hQ₀) Y', ← hxeq, hsq]

end CFSG.OddTranspositions.PartThree.ElevenSp

end
