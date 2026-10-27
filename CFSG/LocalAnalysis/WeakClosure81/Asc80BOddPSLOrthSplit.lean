module

import Mathlib.LinearAlgebra.Matrix.BilinearForm
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZero
import CFSG.HardMathSupport.Foote.ModuleExclusions.OrthEichler
import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
import Mathlib.Tactic.NoncommRing
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.Positivity.Finset

namespace CFSG.LocalAnalysis.WeakClosure81.PSLOuter

open Matrix
open CFSG.HardMathSupport.Foote.ModuleExclusions

private lemma dotProduct_mulVec_comm {k : Type*} [Field k] {n : ℕ}
    {R : Matrix (Fin n) (Fin n) k} (hRs : Rᵀ = R) (u v : Fin n → k) :
    u ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ (R *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hRs, dotProduct_comm]

private lemma refl_mulVec {k : Type*} [Field k] {n : ℕ} {Φ : Matrix (Fin n) (Fin n) k}
    (hΦt : Φᵀ = Φ) (u x : Fin n → k) :
    (1 - (2 / (u ⬝ᵥ (Φ *ᵥ u))) • vecMulVec u (Φ *ᵥ u)) *ᵥ x
      = x - (2 * (u ⬝ᵥ (Φ *ᵥ x)) / (u ⬝ᵥ (Φ *ᵥ u))) • u := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]
  congr 1
  rw [dotProduct_comm ((Φ : Matrix (Fin n) (Fin n) k) *ᵥ u) x,
    ← dotProduct_mulVec_comm hΦt u x]
  ring_nf

private lemma refl_isom_apply {k : Type*} [Field k] {n : ℕ} {Φ : Matrix (Fin n) (Fin n) k}
    (hΦt : Φᵀ = Φ) (u : Fin n → k) (hu : u ⬝ᵥ (Φ *ᵥ u) ≠ 0)
    (x y : Fin n → k) :
    ((1 - (2 / (u ⬝ᵥ (Φ *ᵥ u))) • vecMulVec u (Φ *ᵥ u)) *ᵥ x) ⬝ᵥ
        (Φ *ᵥ ((1 - (2 / (u ⬝ᵥ (Φ *ᵥ u))) • vecMulVec u (Φ *ᵥ u)) *ᵥ y))
      = x ⬝ᵥ (Φ *ᵥ y) := by
  rw [refl_mulVec hΦt, refl_mulVec hΦt]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have hxu : x ⬝ᵥ (Φ *ᵥ u) = u ⬝ᵥ (Φ *ᵥ x) := dotProduct_mulVec_comm hΦt x u
  rw [hxu]
  field_simp [hu]
  ring


private lemma transpose_mul_eq_of_isometry {k : Type*} [Field k] {n : ℕ}
    {Φ Y : Matrix (Fin n) (Fin n) k}
    (h : ∀ x y, (Y *ᵥ x) ⬝ᵥ (Φ *ᵥ (Y *ᵥ y)) = x ⬝ᵥ (Φ *ᵥ y)) :
    Yᵀ * Φ * Y = Φ := by
  have hcomp := Matrix.toBilin'_comp Φ Y Y
  have hfun : (Matrix.toBilin' Φ).comp (Matrix.toLin' Y) (Matrix.toLin' Y) =
      Matrix.toBilin' Φ := by
    apply LinearMap.BilinForm.ext
    intro x y
    simpa only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply',
      Matrix.mulVecLin_apply, Matrix.toBilin'_apply'] using h x y
  rw [hcomp] at hfun
  exact (Matrix.toBilin' (R₁ := k)).injective hfun

private lemma refl_isom {k : Type*} [Field k] {n : ℕ} {Φ : Matrix (Fin n) (Fin n) k}
    (hΦt : Φᵀ = Φ) (u : Fin n → k) (hu : u ⬝ᵥ (Φ *ᵥ u) ≠ 0) :
    (1 - (2 / (u ⬝ᵥ (Φ *ᵥ u))) • vecMulVec u (Φ *ᵥ u))ᵀ * Φ *
      (1 - (2 / (u ⬝ᵥ (Φ *ᵥ u))) • vecMulVec u (Φ *ᵥ u)) = Φ :=
  transpose_mul_eq_of_isometry (refl_isom_apply hΦt u hu)

private lemma refl_mul_self {k : Type*} [Field k] {n : ℕ} {Φ : Matrix (Fin n) (Fin n) k}
    (hΦt : Φᵀ = Φ) (u : Fin n → k) (hu : u ⬝ᵥ (Φ *ᵥ u) ≠ 0) :
    (1 - (2 / (u ⬝ᵥ (Φ *ᵥ u))) • vecMulVec u (Φ *ᵥ u)) *
      (1 - (2 / (u ⬝ᵥ (Φ *ᵥ u))) • vecMulVec u (Φ *ᵥ u)) = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, refl_mulVec hΦt, refl_mulVec hΦt]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul,
    smul_eq_mul]
  field_simp [hu]
  module

private lemma det_refl {k : Type*} [Field k] {n : ℕ} {Φ : Matrix (Fin n) (Fin n) k}
    (u : Fin n → k) (hu : u ⬝ᵥ (Φ *ᵥ u) ≠ 0) :
    (1 - (2 / (u ⬝ᵥ (Φ *ᵥ u))) • vecMulVec u (Φ *ᵥ u)).det = -1 := by
  rw [← smul_vecMulVec, TauCeti.det_one_sub_vecMulVec, dotProduct_smul, smul_eq_mul]
  have hpu : (Φ *ᵥ u) ⬝ᵥ u = u ⬝ᵥ (Φ *ᵥ u) := dotProduct_comm _ _
  rw [hpu]
  field_simp [hu]
  ring


private lemma refl_mul_refl_mulVec {k : Type*} [Field k] {n : ℕ}
    {Φ : Matrix (Fin n) (Fin n) k} (hΦt : Φᵀ = Φ) {u v : Fin n → k} {a : k}
    (huu : u ⬝ᵥ (Φ *ᵥ u) = a) (hvv : v ⬝ᵥ (Φ *ᵥ v) = a)
    (huv : u ⬝ᵥ (Φ *ᵥ v) = 0) (ha : a ≠ 0) (h2 : (2 : k) ≠ 0) (x : Fin n → k) :
    (2 * a) • (((1 - (2 / ((u + v) ⬝ᵥ (Φ *ᵥ (u + v)))) • vecMulVec (u + v) (Φ *ᵥ (u + v))) *
      (1 - (2 / ((u - v) ⬝ᵥ (Φ *ᵥ (u - v)))) • vecMulVec (u - v) (Φ *ᵥ (u - v)))) *ᵥ x)
      = (2 * a) • x - (4 : k) • ((u ⬝ᵥ (Φ *ᵥ x)) • u + (v ⬝ᵥ (Φ *ᵥ x)) • v) := by
  have hvu : v ⬝ᵥ (Φ *ᵥ u) = 0 := by
    rw [dotProduct_mulVec_comm hΦt v u]; exact huv
  have hsum : (u + v) ⬝ᵥ (Φ *ᵥ (u + v)) = 2 * a := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, huu, hvu, huv, hvv]
    ring
  have hdiff : (u - v) ⬝ᵥ (Φ *ᵥ (u - v)) = 2 * a := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, huu, hvu, huv, hvv]
    ring
  have hwz : (u + v) ⬝ᵥ (Φ *ᵥ (u - v)) = 0 := by
    rw [Matrix.mulVec_sub, dotProduct_sub, add_dotProduct, add_dotProduct, huu, hvu, huv, hvv]
    ring
  rw [← Matrix.mulVec_mulVec, refl_mulVec hΦt (u + v), refl_mulVec hΦt (u - v),
    hsum, hdiff]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    add_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, smul_sub, huu, hvv, huv, hvu,
    mul_assoc]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  field_simp [ha, h2]
  ring


private lemma smul_inv_smul_cancel {k : Type*} [Field k] {V : Type*} [AddCommGroup V]
    [Module k V] {c : k} (hc : c ≠ 0) (v : V) : c⁻¹ • (c • v) = v := by
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

private lemma refl_mul_refl_mulVec_div {k : Type*} [Field k] {n : ℕ}
    {Φ : Matrix (Fin n) (Fin n) k} (hΦt : Φᵀ = Φ) {u v : Fin n → k} {a : k}
    (huu : u ⬝ᵥ (Φ *ᵥ u) = a) (hvv : v ⬝ᵥ (Φ *ᵥ v) = a)
    (huv : u ⬝ᵥ (Φ *ᵥ v) = 0) (ha : a ≠ 0) (h2 : (2 : k) ≠ 0) (x : Fin n → k) :
    (((1 - (2 / ((u + v) ⬝ᵥ (Φ *ᵥ (u + v)))) • vecMulVec (u + v) (Φ *ᵥ (u + v))) *
      (1 - (2 / ((u - v) ⬝ᵥ (Φ *ᵥ (u - v)))) • vecMulVec (u - v) (Φ *ᵥ (u - v)))) *ᵥ x)
      = x - ((2 * a)⁻¹ * 4) • ((u ⬝ᵥ (Φ *ᵥ x)) • u + (v ⬝ᵥ (Φ *ᵥ x)) • v) := by
  have hc : (2 * a) ≠ 0 := mul_ne_zero h2 ha
  calc
    (((1 - (2 / ((u + v) ⬝ᵥ (Φ *ᵥ (u + v)))) • vecMulVec (u + v) (Φ *ᵥ (u + v))) *
      (1 - (2 / ((u - v) ⬝ᵥ (Φ *ᵥ (u - v)))) • vecMulVec (u - v) (Φ *ᵥ (u - v)))) *ᵥ x)
        = (2 * a)⁻¹ • ((2 * a) • ((((1 - (2 / ((u + v) ⬝ᵥ (Φ *ᵥ (u + v)))) •
            vecMulVec (u + v) (Φ *ᵥ (u + v))) *
          (1 - (2 / ((u - v) ⬝ᵥ (Φ *ᵥ (u - v)))) • vecMulVec (u - v) (Φ *ᵥ (u - v)))) *ᵥ x))) :=
          (smul_inv_smul_cancel hc _).symm
    _ = (2 * a)⁻¹ • ((2 * a) • x -
          (4 : k) • ((u ⬝ᵥ (Φ *ᵥ x)) • u + (v ⬝ᵥ (Φ *ᵥ x)) • v)) := by
          rw [refl_mul_refl_mulVec hΦt huu hvv huv ha h2 x]
    _ = x - ((2 * a)⁻¹ * 4) • ((u ⬝ᵥ (Φ *ᵥ x)) • u + (v ⬝ᵥ (Φ *ᵥ x)) • v) := by
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul, smul_smul]


private lemma refl_conj {k : Type*} [Field k] {n : ℕ} {Φ : Matrix (Fin n) (Fin n) k}
    (hΦt : Φᵀ = Φ) {A : Matrix (Fin n) (Fin n) k} (hA2 : A * A = 1)
    (hisom : ∀ x y, (A *ᵥ x) ⬝ᵥ (Φ *ᵥ (A *ᵥ y)) = x ⬝ᵥ (Φ *ᵥ y))
    (u : Fin n → k) :
    A * (1 - (2 / (u ⬝ᵥ (Φ *ᵥ u))) • vecMulVec u (Φ *ᵥ u)) * A
      = 1 - (2 / ((A *ᵥ u) ⬝ᵥ (Φ *ᵥ (A *ᵥ u)))) •
          vecMulVec (A *ᵥ u) (Φ *ᵥ (A *ᵥ u)) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [refl_mulVec hΦt u, refl_mulVec hΦt (A *ᵥ u)]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA2,
    Matrix.one_mulVec]
  have h1 : u ⬝ᵥ ((Φ * A) *ᵥ x) = (A *ᵥ u) ⬝ᵥ (Φ *ᵥ x) := by
    simpa only [Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec] using (hisom u (A *ᵥ x)).symm
  have h2 : u ⬝ᵥ (Φ *ᵥ u) = (A *ᵥ u) ⬝ᵥ ((Φ * A) *ᵥ u) := by
    simpa only [Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec] using (hisom u u).symm
  rw [h1, h2]


private lemma pair_span_lt_top {K : Type*} [Field K] {n : ℕ} (hn : 3 ≤ n) (v u : Fin n → K) :
    Submodule.span K ({v, u} : Set (Fin n → K)) < ⊤ := by
  classical
  have h := finrank_span_finset_le_card (R := K) ({v, u} : Finset (Fin n → K))
  have hcard : ({v, u} : Finset (Fin n → K)).card ≤ 2 := by
    simpa using Finset.card_insert_le v ({u} : Finset (Fin n → K))
  have hle : Set.finrank K ({v, u} : Set (Fin n → K)) ≤ 2 := by
    rw [← Finset.coe_pair]
    exact le_trans h hcard
  rw [lt_top_iff_ne_top]
  intro htop
  have h2 : Module.finrank K (⊤ : Submodule K (Fin n → K)) ≤ 2 := htop ▸ hle
  rw [finrank_top K (Fin n → K), Module.finrank_fin_fun] at h2
  omega



private lemma exists_eigen_other {k : Type} [Field k] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) k} (hA2 : A * A = 1) (h2 : (2 : k) ≠ 0) {ε : k}
    (hε : ε = 1 ∨ ε = -1) (hA : A ≠ ε • 1) :
    ∃ t : Fin n → k, A *ᵥ t = -ε • t ∧ t ≠ 0 := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hex : ∃ y : Fin n → k, A *ᵥ y ≠ ε • y := by
    by_contra h
    push Not at h
    apply hA
    apply Matrix.ext_iff_mulVec.mpr
    intro y
    simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using h y
  obtain ⟨y, hy⟩ := hex
  refine ⟨(2 : k)⁻¹ • (y - ε • (A *ᵥ y)), ?_, ?_⟩
  · simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec, smul_sub, smul_smul]
    have hcoef : -ε * (2⁻¹ * ε) = -(2⁻¹) := by
      rw [show -ε * (2⁻¹ * ε) = -(2⁻¹ * (ε * ε)) by ring, hε2, mul_one]
    rw [hcoef]
    module
  · intro ht
    apply hy
    have hW : y - ε • (A *ᵥ y) = 0 := by
      have h' : (2 : k)⁻¹ • (y - ε • (A *ᵥ y)) = 0 := by simpa using ht
      exact (smul_eq_zero.mp h').resolve_left (inv_ne_zero h2)
    have hyeq : y = ε • (A *ᵥ y) := sub_eq_zero.mp hW
    calc A *ᵥ y = A *ᵥ (ε • (A *ᵥ y)) := by conv_lhs => rw [hyeq]
      _ = ε • (A *ᵥ (A *ᵥ y)) := by rw [Matrix.mulVec_smul]
      _ = ε • y := by rw [Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec]

private lemma isom_orthogonal_of_opposite_eigen {k : Type} [Field k] {n : ℕ}
    {Φ A : Matrix (Fin n) (Fin n) k}
    (hisom : ∀ x y, (A *ᵥ x) ⬝ᵥ (Φ *ᵥ (A *ᵥ y)) = x ⬝ᵥ (Φ *ᵥ y))
    {s t : Fin n → k} {ε : k} (hsA : A *ᵥ s = ε • s) (htA : A *ᵥ t = -ε • t)
    (hε2 : ε * ε = 1) (h2 : (2 : k) ≠ 0) :
    s ⬝ᵥ (Φ *ᵥ t) = 0 := by
  have hiso := hisom s t
  rw [hsA, htA, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_smul] at hiso
  have hneg : s ⬝ᵥ (Φ *ᵥ t) = -(s ⬝ᵥ (Φ *ᵥ t)) := by
    have hεneg : ε * -ε = -1 := by linear_combination -hε2
    rw [hεneg, neg_one_smul] at hiso
    exact neg_eq_iff_eq_neg.mp hiso
  have htwo : (2 : k) * (s ⬝ᵥ (Φ *ᵥ t)) = 0 := by
    rw [two_mul]
    nth_rewrite 1 [hneg]
    exact neg_add_cancel _
  exact (mul_eq_zero.mp htwo).resolve_left h2


private lemma exists_bilin_ne_zero_of_det {k : Type} [Field k] {n : ℕ}
    {Φ : Matrix (Fin n) (Fin n) k} (hΦ : IsUnit Φ.det) {s : Fin n → k} (hs : s ≠ 0) :
    ∃ x : Fin n → k, s ⬝ᵥ (Φ *ᵥ x) ≠ 0 := by
  by_contra h
  push Not at h
  have hnd : (Matrix.toBilin' Φ).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hΦ.ne_zero
  apply hs
  apply hnd.1 s
  intro y
  rw [Matrix.toBilin'_apply']
  exact h y

private lemma refl_mul_refl_comm {k : Type} [Field k] {n : ℕ}
    {Φ A : Matrix (Fin n) (Fin n) k}
    (hisom : ∀ x y, (A *ᵥ x) ⬝ᵥ (Φ *ᵥ (A *ᵥ y)) = x ⬝ᵥ (Φ *ᵥ y))
    {u v : Fin n → k} {c : k} (huA : A *ᵥ u = u) (hvA : A *ᵥ v = -v)
    (hD : ∀ x : Fin n → k,
      ((1 - (2 / ((u + v) ⬝ᵥ (Φ *ᵥ (u + v)))) • vecMulVec (u + v) (Φ *ᵥ (u + v))) *
        (1 - (2 / ((u - v) ⬝ᵥ (Φ *ᵥ (u - v)))) • vecMulVec (u - v) (Φ *ᵥ (u - v)))) *ᵥ x
        = x - c • ((u ⬝ᵥ (Φ *ᵥ x)) • u + (v ⬝ᵥ (Φ *ᵥ x)) • v)) :
    ((1 - (2 / ((u + v) ⬝ᵥ (Φ *ᵥ (u + v)))) • vecMulVec (u + v) (Φ *ᵥ (u + v))) *
      (1 - (2 / ((u - v) ⬝ᵥ (Φ *ᵥ (u - v)))) • vecMulVec (u - v) (Φ *ᵥ (u - v)))) * A
      = A * ((1 - (2 / ((u + v) ⬝ᵥ (Φ *ᵥ (u + v)))) • vecMulVec (u + v) (Φ *ᵥ (u + v))) *
        (1 - (2 / ((u - v) ⬝ᵥ (Φ *ᵥ (u - v)))) • vecMulVec (u - v) (Φ *ᵥ (u - v)))) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [← Matrix.mulVec_mulVec, hD (A *ᵥ x)]
  conv_rhs => rw [← Matrix.mulVec_mulVec]
  rw [hD x, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, huA, hvA, smul_neg]
  have hBu : u ⬝ᵥ (Φ *ᵥ (A *ᵥ x)) = u ⬝ᵥ (Φ *ᵥ x) := by
    have h := hisom u x
    rwa [huA] at h
  have hBv : v ⬝ᵥ (Φ *ᵥ (A *ᵥ x)) = -(v ⬝ᵥ (Φ *ᵥ x)) := by
    have h := hisom v x
    rw [hvA, neg_dotProduct] at h
    linear_combination -h
  rw [hBu, hBv, neg_smul]

public section

theorem orth_conj_or_inverted_unipotent_of_sq {k : Type} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) {n : ℕ} (hn : 3 ≤ n) {A Φ : Matrix (Fin n) (Fin n) k}
    (hΦ : IsUnit Φ.det) (hΦt : Φᵀ = Φ) (hA2 : A * A = 1) (hA : ∀ c : k, A ≠ c • 1)
    (hAΦ : Aᵀ * Φ = Φ * A) :
    (∃ g : Matrix (Fin n) (Fin n) k, gᵀ * Φ * g = Φ ∧ g.det = 1 ∧
        g * A * g⁻¹ * A = A * (g * A * g⁻¹) ∧ ∀ c : k, g * A * g⁻¹ ≠ c • A) ∨
      ∃ Y : Matrix (Fin n) (Fin n) k, Y ≠ 1 ∧ (Y - 1) ^ 3 = 0 ∧ Yᵀ * Φ * Y = Φ ∧
        A * Y * A⁻¹ = Y⁻¹ := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hAΦA : Aᵀ * Φ * A = Φ := by
    rw [hAΦ, Matrix.mul_assoc, hA2, Matrix.mul_one]
  have hAisom : ∀ x y, (A *ᵥ x) ⬝ᵥ (Φ *ᵥ (A *ᵥ y)) = x ⬝ᵥ (Φ *ᵥ y) := by
    have hcomp := Matrix.toBilin'_comp Φ A A
    rw [hAΦA] at hcomp
    intro x y
    have := congrArg (fun f => f x y) hcomp
    simpa only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply',
      Matrix.mulVecLin_apply, Matrix.toBilin'_apply'] using this
  obtain ⟨z, hz0, hzq⟩ :=
    CFSG.FiniteField.exists_ne_zero_dotProduct_mulVec_eq_zero (K := k) (σ := Fin n)
      (by simpa using hn) (Φ * A)
  have hzq' : z ⬝ᵥ (Φ *ᵥ (A *ᵥ z)) = 0 := by
    simpa only [← Matrix.mulVec_mulVec] using hzq
  let u : Fin n → k := (2 : k)⁻¹ • (z + A *ᵥ z)
  let v : Fin n → k := (2 : k)⁻¹ • (z - A *ᵥ z)
  have huA : A *ᵥ u = u := by
    simp only [u]
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_mulVec, hA2,
      Matrix.one_mulVec, add_comm]
  have hvA : A *ᵥ v = -v := by
    simp only [v]
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hA2,
      Matrix.one_mulVec, ← smul_neg]
    congr 1
    abel
  have huz : u + v = z := by
    simp only [u, v]
    rw [← smul_add]
    have h : (z + A *ᵥ z) + (z - A *ᵥ z) = (2 : k) • z := by module
    rw [h, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hAzAz : (A *ᵥ z) ⬝ᵥ (Φ *ᵥ (A *ᵥ z)) = z ⬝ᵥ (Φ *ᵥ z) := hAisom z z
  have hAz_z : (A *ᵥ z) ⬝ᵥ (Φ *ᵥ z) = 0 := by
    rw [dotProduct_mulVec_comm hΦt]
    exact hzq'
  let a : k := u ⬝ᵥ (Φ *ᵥ u)
  have huu : u ⬝ᵥ (Φ *ᵥ u) = a := rfl
  have hvv : v ⬝ᵥ (Φ *ᵥ v) = a := by
    have hcalc : v ⬝ᵥ (Φ *ᵥ v) =
        (2 : k)⁻¹ ^ 2 * (2 * (z ⬝ᵥ (Φ *ᵥ z))) := by
      simp only [v, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hAzAz, hzq', hAz_z]
      ring
    have huucalc : u ⬝ᵥ (Φ *ᵥ u) =
        (2 : k)⁻¹ ^ 2 * (2 * (z ⬝ᵥ (Φ *ᵥ z))) := by
      simp only [u, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hAzAz, hzq', hAz_z]
      ring
    rw [hcalc]
    exact huucalc.symm
  have huv : u ⬝ᵥ (Φ *ᵥ v) = 0 := by
    simp only [u, v, Matrix.mulVec_sub, Matrix.mulVec_smul, add_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hAzAz, hzq', hAz_z]
    ring
  by_cases ha : a = 0
  ·
    have hzuv : z = u + v := huz.symm
    have huv_ne : u ≠ 0 ∨ v ≠ 0 := by
      by_contra h
      push Not at h
      apply hz0
      rw [hzuv, h.1, h.2, add_zero]
    obtain ⟨s, ε, hε, hsA, hs0, hss⟩ : ∃ (s : Fin n → k) (ε : k),
        (ε = 1 ∨ ε = -1) ∧ A *ᵥ s = ε • s ∧ s ≠ 0 ∧ s ⬝ᵥ (Φ *ᵥ s) = 0 := by
      rcases huv_ne with hu | hv
      · refine ⟨u, 1, Or.inl rfl, ?_, hu, ?_⟩
        · simpa using huA
        · rw [huu, ha]
      · refine ⟨v, -1, Or.inr rfl, ?_, hv, ?_⟩
        · simpa only [neg_one_smul] using hvA
        · rw [hvv, ha]
    have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    obtain ⟨t, htA, ht0⟩ := exists_eigen_other hA2 h2 hε (hA ε)
    have hst : s ⬝ᵥ (Φ *ᵥ t) = 0 := isom_orthogonal_of_opposite_eigen hAisom hsA htA hε2 h2
    let B : LinearMap.BilinForm k (Fin n → k) := Matrix.toBilin' Φ
    have hBapp : ∀ x y, B x y = x ⬝ᵥ (Φ *ᵥ y) := fun x y => Matrix.toBilin'_apply' _ _ _
    have hsymm : ∀ x y, B x y = B y x := by
      intro x y
      rw [hBapp, hBapp]
      exact dotProduct_mulVec_comm hΦt x y
    have hssB : B s s = 0 := by rw [hBapp]; exact hss
    have hstB : B s t = 0 := by rw [hBapp]; exact hst
    let U : GL (Fin n) k := eichU B s t
    let Y : Matrix (Fin n) (Fin n) k := (U : Matrix (Fin n) (Fin n) k)
    have hU_mulVec : ∀ x, Y *ᵥ x = eichLin B s t x := by
      intro x
      simpa only [Y, U] using eichU_mulVec hsymm h2 hssB hstB x
    have hU_mem : U ∈ isomGroup B := by simpa only [U] using eichU_mem hsymm h2 hssB hstB
    have hYisom : ∀ x y, (Y *ᵥ x) ⬝ᵥ (Φ *ᵥ (Y *ᵥ y)) = x ⬝ᵥ (Φ *ᵥ y) := by
      intro x y
      have h := (mem_isomGroup_iff.mp hU_mem) x y
      simpa only [Y, hBapp] using h
    have hYΦ : Yᵀ * Φ * Y = Φ := transpose_mul_eq_of_isometry hYisom
    let N : Module.End k (Fin n → k) := eichLin B s t - 1
    have hYm1 : Y - 1 = LinearMap.toMatrix' N := by
      apply Matrix.ext_iff_mulVec.mpr
      intro x
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, LinearMap.toMatrix'_mulVec,
        hU_mulVec x]
      rfl
    have hN_apply : ∀ y, N y =
        (B s y) • t - (B t y + qd B t * B s y) • s := by
      intro y
      change eichLin B s t y - y =
        (B s y) • t - (B t y + qd B t * B s y) • s
      rw [eichLin_apply, add_smul]
      abel
    have hNs : N s = 0 := by
      rw [hN_apply]
      simp [hssB, hsymm t s, hstB]
    have hNt : N t = -(B t t) • s := by
      rw [hN_apply]
      simp [hstB]
    have hN2 : ∀ y, N (N y) = -((B s y) * (B t t)) • s := by
      intro y
      have hy : N y = (B s y) • t - (B t y + qd B t * B s y) • s := hN_apply y
      rw [hy, map_sub, map_smul, map_smul, hNt, hNs, smul_zero, sub_zero, smul_smul]
      congr 1
      ring
    have hN3 : N * N * N = 0 := by
      apply LinearMap.ext
      intro y
      calc (N * N * N) y = N (N (N y)) := by rw [Module.End.mul_apply, Module.End.mul_apply]
        _ = N (-((B s y) * (B t t)) • s) := by rw [hN2 y]
        _ = -((B s y) * (B t t)) • N s := by rw [map_smul]
        _ = 0 := by rw [hNs, smul_zero]
    have hY3 : (Y - 1) ^ 3 = 0 := by
      have h3 : (Y - 1) * (Y - 1) * (Y - 1) = 0 := by
        rw [hYm1, ← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_mul,
          show N * N * N = 0 from hN3]
        simp
      simpa only [pow_three, mul_assoc] using h3
    have hY_ne : Y ≠ 1 := by
      intro hY1
      have hNid : ∀ y, eichLin B s t y = y := by
        intro y
        have h := congrArg (fun M => M *ᵥ y) hY1
        simpa only [Y, U, eichU_mulVec hsymm h2 hssB hstB y, Matrix.one_mulVec] using h
      have hBtt : B t t = 0 := by
        have h := hNid t
        rw [eichLin_apply] at h
        simp only [hstB, zero_smul, mul_zero, add_zero, sub_zero] at h
        have h' : B t t • s = 0 := sub_eq_self.mp h
        exact (smul_eq_zero.mp h').resolve_right hs0
      have hlineq : ∀ y, B s y • t = B t y • s := by
        intro y
        have h := hNid y
        have hqd : qd B t = 0 := by simp [qd, hBtt]
        rw [eichLin_apply, hqd] at h
        simp only [zero_mul, zero_smul, sub_zero] at h
        have h' : y + (B s y • t - B t y • s) = y + 0 := by
          rw [add_zero]
          simpa only [sub_eq_add_neg, add_assoc] using h
        exact sub_eq_zero.mp (add_left_cancel h')
      obtain ⟨x0, hx0⟩ := exists_bilin_ne_zero_of_det hΦ hs0
      have hlin0 := hlineq x0
      let c0 : k := B t x0 / B s x0
      have ht_eq : t = c0 • s := by
        have h' : (B s x0) • t = (B t x0) • s := hlin0
        have hBs0 : B s x0 ≠ 0 := by rw [hBapp]; exact hx0
        have h := congrArg (fun y => (B s x0)⁻¹ • y) h'
        rw [smul_smul, smul_smul, inv_mul_cancel₀ hBs0, one_smul] at h
        calc t = ((B s x0)⁻¹ * B t x0) • s := h
          _ = c0 • s := by simp only [c0, div_eq_mul_inv, mul_comm]
      have hceq : c0 • (ε • s) = (-ε) • (c0 • s) := by
        calc c0 • (ε • s) = A *ᵥ t := by rw [ht_eq, Matrix.mulVec_smul, hsA]
          _ = -ε • t := htA
          _ = (-ε) • (c0 • s) := by rw [ht_eq]
      have hzero : (2 * ε * c0) • s = 0 := by
        rw [smul_smul, smul_smul, mul_comm c0 ε, neg_mul] at hceq
        have hsub : ((ε * c0) - (-(ε * c0))) • s = 0 := by
          rw [sub_smul, hceq, sub_self]
        have hcoef : 2 * ε * c0 = (ε * c0) - (-(ε * c0)) := by ring
        rwa [hcoef]
      have hcoef0 : 2 * ε * c0 = 0 := (smul_eq_zero.mp hzero).resolve_right hs0
      have hc0 : c0 = 0 := by
        have h2e : (2 : k) * ε ≠ 0 := mul_ne_zero h2 hε0
        exact (mul_eq_zero.mp hcoef0).resolve_left h2e
      exact ht0 (by rw [ht_eq, hc0, zero_smul])
    let AU : GL (Fin n) k := ⟨A, A, hA2, hA2⟩
    have hAUval : (AU : Matrix (Fin n) (Fin n) k) = A := rfl
    have hAUmem : AU ∈ isomGroup B := by
      rw [mem_isomGroup_iff]
      intro y z
      simpa only [hAUval, hBapp] using hAisom y z
    have hAU_sq : AU * AU = 1 := by
      apply Units.ext
      simp only [Units.val_mul, hAUval, Units.val_one]
      exact hA2
    have hAU_inv : AU⁻¹ = AU := inv_eq_of_mul_eq_one_right hAU_sq
    have hconj := eichU_conj (B := B) (g := AU) hsymm h2 hAUmem hssB hstB
    have hconj' : AU * eichU B s t * AU⁻¹ = eichU B s (-t) := by
      calc AU * eichU B s t * AU⁻¹ =
          eichU B ((AU : Matrix (Fin n) (Fin n) k) *ᵥ s)
            ((AU : Matrix (Fin n) (Fin n) k) *ᵥ t) := hconj
        _ = eichU B (ε • s) ((-ε) • t) := by rw [hAUval, hsA, htA]
        _ = eichU B s ((ε * -ε) • t) := by rw [eichU_scale]
        _ = eichU B s (-t) := by
            rw [show ε * -ε = -1 by linear_combination -hε2, neg_one_smul]
    have hmat := congrArg Units.val hconj'
    have hleft : ((AU * eichU B s t * AU⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        A * Y * A := by
      simp only [Units.val_mul, hAUval, hAU_inv, Y, U]
    have hright : ((eichU B s (-t) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Y⁻¹ := by
      rw [← eichU_inv hsymm h2 hssB hstB, GeneralLinearGroup.coe_inv]
    have hAY : A * Y * A = Y⁻¹ := by
      rw [← hleft, hmat, hright]
    have hAinv : A⁻¹ = A := Matrix.inv_eq_left_inv hA2
    refine Or.inr ⟨Y, hY_ne, hY3, hYΦ, ?_⟩
    rw [hAinv]
    exact hAY
  ·
    have hu_ne : u ≠ 0 := by
      intro h
      apply ha
      rw [← huu, h]
      simp
    have hvu : v ⬝ᵥ (Φ *ᵥ u) = 0 := by
      rw [dotProduct_mulVec_comm hΦt v u]
      exact huv
    have hdiffa : (u - v) ⬝ᵥ (Φ *ᵥ (u - v)) = 2 * a := by
      rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, huu, hvu,
        huv, hvv]
      ring
    have hdiff_ne : (u - v) ⬝ᵥ (Φ *ᵥ (u - v)) ≠ 0 := by
      rw [hdiffa]
      exact mul_ne_zero h2 ha
    let R : (Fin n → k) → Matrix (Fin n) (Fin n) k := fun x =>
      1 - (2 / (x ⬝ᵥ (Φ *ᵥ x))) • vecMulVec x (Φ *ᵥ x)
    let r1 : Matrix (Fin n) (Fin n) k := R u
    let r2 : Matrix (Fin n) (Fin n) k := R (u - v)
    have hr1_isom : r1ᵀ * Φ * r1 = Φ := by
      simpa only [r1, R] using refl_isom hΦt u (by rw [huu]; exact ha)
    have hr2_isom : r2ᵀ * Φ * r2 = Φ := by
      simpa only [r2, R] using refl_isom hΦt (u - v) hdiff_ne
    have hr1_sq : r1 * r1 = 1 := by
      simpa only [r1, R] using refl_mul_self hΦt u (by rw [huu]; exact ha)
    have hr2_sq : r2 * r2 = 1 := by
      simpa only [r2, R] using refl_mul_self hΦt (u - v) hdiff_ne
    have hr1_det : r1.det = -1 := by
      simpa only [r1, R] using det_refl u (by rw [huu]; exact ha)
    have hr2_det : r2.det = -1 := by
      simpa only [r2, R] using det_refl (u - v) hdiff_ne
    have hAuv : A *ᵥ (u - v) = u + v := by
      rw [Matrix.mulVec_sub, huA, hvA, sub_neg_eq_add]
    have hA_r1 : A * r1 * A = r1 := by
      have hc := refl_conj hΦt hA2 hAisom u
      simpa only [r1, R, huA] using hc
    have hA_r2 : A * r2 * A = R (u + v) := by
      have hc := refl_conj hΦt hA2 hAisom (u - v)
      simpa only [r2, R, hAuv] using hc
    have hA_r2_mul : r2 * A = A * R (u + v) := by
      calc r2 * A = (A * A) * (r2 * A) := by rw [hA2, Matrix.one_mul]
        _ = A * (A * r2 * A) := by noncomm_ring
        _ = A * R (u + v) := by rw [hA_r2]
    have hr1_comm : r1 * A = A * r1 := by
      calc r1 * A = (A * A) * (r1 * A) := by rw [hA2, Matrix.one_mul]
        _ = A * (A * r1 * A) := by noncomm_ring
        _ = A * r1 := by rw [hA_r1]
    let D : Matrix (Fin n) (Fin n) k := R (u + v) * R (u - v)
    have hD_formula : ∀ x : Fin n → k,
        (R (u + v) * R (u - v)) *ᵥ x = x - ((2 * a)⁻¹ * 4) •
          ((u ⬝ᵥ (Φ *ᵥ x)) • u + (v ⬝ᵥ (Φ *ᵥ x)) • v) := by
      intro x
      simpa only [R] using refl_mul_refl_mulVec_div hΦt huu hvv huv ha h2 x
    have hD_comm : D * A = A * D := by
      change (R (u + v) * R (u - v)) * A = A * (R (u + v) * R (u - v))
      refine refl_mul_refl_comm hAisom huA hvA (c := (2 * a)⁻¹ * 4) ?_
      intro x
      simpa only [R] using hD_formula x
    have hA'_eq : (r2 * r1) * A * (r1 * r2) = A * D := by
      calc (r2 * r1) * A * (r1 * r2)
          = r2 * (r1 * A * r1) * r2 := by noncomm_ring
        _ = r2 * A * r2 := by
            rw [show r1 * A * r1 = A by
              rw [hr1_comm, Matrix.mul_assoc, hr1_sq, Matrix.mul_one]]
        _ = A * R (u + v) * r2 := by rw [hA_r2_mul]
        _ = A * D := by
            change A * R (u + v) * R (u - v) =
              A * (R (u + v) * R (u - v))
            rw [Matrix.mul_assoc]
    let g : Matrix (Fin n) (Fin n) k := r2 * r1
    have hgg : g * (r1 * r2) = 1 := by
      change (r2 * r1) * (r1 * r2) = 1
      calc (r2 * r1) * (r1 * r2) = r2 * (r1 * r1) * r2 := by noncomm_ring
        _ = r2 * 1 * r2 := by rw [hr1_sq]
        _ = r2 * r2 := by rw [Matrix.mul_one]
        _ = 1 := hr2_sq
    have hginv : g⁻¹ = r1 * r2 := by
      change (r2 * r1)⁻¹ = r1 * r2
      exact Matrix.inv_eq_right_inv hgg
    have hg_isom : gᵀ * Φ * g = Φ := by
      change (r2 * r1)ᵀ * Φ * (r2 * r1) = Φ
      rw [Matrix.transpose_mul]
      calc r1ᵀ * r2ᵀ * Φ * (r2 * r1)
          = r1ᵀ * (r2ᵀ * Φ * r2) * r1 := by noncomm_ring
        _ = r1ᵀ * Φ * r1 := by rw [hr2_isom]
        _ = Φ := hr1_isom
    have hg_det : g.det = 1 := by
      change (r2 * r1).det = 1
      rw [Matrix.det_mul, hr2_det, hr1_det]
      ring
    have hAA' : A * (g * A * g⁻¹) = D := by
      rw [hginv]
      change A * ((r2 * r1) * A * (r1 * r2)) = D
      calc A * ((r2 * r1) * A * (r1 * r2))
          = A * (A * D) := by rw [hA'_eq]
        _ = D := by rw [← Matrix.mul_assoc, hA2, Matrix.one_mul]
    have hA'comm : g * A * g⁻¹ * A = A * (g * A * g⁻¹) := by
      rw [hginv]
      change (r2 * r1) * A * (r1 * r2) * A =
        A * ((r2 * r1) * A * (r1 * r2))
      calc (r2 * r1) * A * (r1 * r2) * A
          = (A * D) * A := by rw [hA'_eq]
        _ = A * (D * A) := by noncomm_ring
        _ = A * (A * D) := by rw [hD_comm]
        _ = A * ((r2 * r1) * A * (r1 * r2)) := by
            rw [← hA'_eq]
    have hA'_nonscalar : ∀ c : k, g * A * g⁻¹ ≠ c • A := by
      intro c hc
      have hD_eq : D = c • 1 := by
        calc D = A * (g * A * g⁻¹) := hAA'.symm
          _ = A * (c • A) := by rw [hc]
          _ = c • (A * A) := by rw [Matrix.mul_smul]
          _ = c • 1 := by rw [hA2]
      have hdu : D *ᵥ u = -u := by
        rw [hD_formula u, huu, hvu, zero_smul, add_zero, smul_smul]
        have hcoef : (2 * a)⁻¹ * 4 * a = 2 := by
          field_simp [ha, h2]
          ring
        rw [hcoef]
        module
      have hcu : c • u = -u := by
        have h := congrArg (fun M => M *ᵥ u) hD_eq
        simpa [Matrix.smul_mulVec, Matrix.one_mulVec, hdu] using h.symm
      have hc1 : c = -1 := by
        have hh : (c + 1) • u = 0 := by
          rw [add_smul, hcu, one_smul]
          abel
        have h0 : c + 1 = 0 := (smul_eq_zero.mp hh).resolve_right hu_ne
        linear_combination h0
      have hDneg : D = -1 := by
        rw [hD_eq, hc1, neg_one_smul]
      have hxspan : ∀ x : Fin n → k,
          x ∈ Submodule.span k ({u, v} : Set (Fin n → k)) := by
        intro x
        let T : Fin n → k := (u ⬝ᵥ (Φ *ᵥ x)) • u + (v ⬝ᵥ (Φ *ᵥ x)) • v
        have h1 : D *ᵥ x = -x := by rw [hDneg, Matrix.neg_mulVec, Matrix.one_mulVec]
        have h2x : x - ((2 * a)⁻¹ * 4) • T = -x := by
          rw [← hD_formula x, h1]
        have h3 : (2 : k) • x = ((2 * a)⁻¹ * 4) • T := by
          rw [two_smul]
          linear_combination h2x
        have hx : x = ((2 : k)⁻¹ * ((2 * a)⁻¹ * 4)) • T := by
          calc x = (2 : k)⁻¹ • ((2 : k) • x) := (smul_inv_smul_cancel h2 x).symm
            _ = (2 : k)⁻¹ • (((2 * a)⁻¹ * 4) • T) := by rw [h3]
            _ = ((2 : k)⁻¹ * ((2 * a)⁻¹ * 4)) • T := by rw [smul_smul]
        rw [hx]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      have htop : (⊤ : Submodule k (Fin n → k)) ≤
          Submodule.span k ({u, v} : Set (Fin n → k)) := fun x _ => hxspan x
      exact (not_le_of_gt (pair_span_lt_top hn u v)) htop
    exact Or.inl ⟨g, hg_isom, hg_det, hA'comm, hA'_nonscalar⟩

end

end CFSG.LocalAnalysis.WeakClosure81.PSLOuter
