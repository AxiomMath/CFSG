module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Center
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

private lemma exists_indep_of_not_scalar {A : Matrix (Fin n) (Fin n) K}
    (hA : ∀ d : K, A ≠ d • 1) :
    ∃ v : Fin n → K, LinearIndependent K ![v, A *ᵥ v] := by
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := A.mulVecLin) h
  apply hA a
  apply Matrix.ext_of_mulVec_single
  intro i
  have hx := DFunLike.congr_fun ha (Pi.single i 1)
  have hx' : A *ᵥ Pi.single i (1 : K) = a • Pi.single i 1 := by
    simpa [Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.one_mulVec] using hx
  rw [hx']
  ext j
  by_cases h : i = j <;> simp [Matrix.col, Matrix.smul_apply, h]

private lemma pair_span_lt_top (hn : 3 ≤ n) (v u : Fin n → K) :
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

private lemma functional_dotProduct (f : (Fin n → K) →ₗ[K] K) (x ψ : Fin n → K)
    (hψ : ∀ j, ψ j = f (Pi.single j 1)) : f x = ψ ⬝ᵥ x := by
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  simp only [dotProduct, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (fun j => if i = j then (1 : K) else 0) = Pi.single i 1 from by
    funext j
    rw [Pi.single_apply]
    exact if_congr eq_comm rfl rfl]
  rw [← hψ i]
  exact mul_comm _ _

@[expose] def IsRankTwoSqZero (N : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ w₁ w₂ φ₁ φ₂ : Fin n → K, φ₁ ⬝ᵥ w₁ = 0 ∧ φ₁ ⬝ᵥ w₂ = 0 ∧ φ₂ ⬝ᵥ w₁ = 0 ∧ φ₂ ⬝ᵥ w₂ = 0 ∧
    N = vecMulVec w₁ φ₁ + vecMulVec w₂ φ₂

theorem IsRankTwoSqZero.mul_self_eq_zero {N : Matrix (Fin n) (Fin n) K}
    (h : IsRankTwoSqZero N) : N * N = 0 := by
  obtain ⟨w₁, w₂, φ₁, φ₂, h11, h12, h21, h22, rfl⟩ := h
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.vecMulVec_mul_vecMulVec, h11, h12, h21, h22,
    zero_smul, Matrix.vecMulVec_zero, add_zero]

theorem exists_rankTwo_anticomm (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) K} {c : K}
    (hA2 : A * A = c • 1) (hA : ∀ d : K, A ≠ d • 1) :
    ∃ N : Matrix (Fin n) (Fin n) K, N ≠ 0 ∧ IsRankTwoSqZero N ∧ A * N = -(N * A) := by
  obtain ⟨v, hLI⟩ := exists_indep_of_not_scalar hA
  let u := A *ᵥ v
  have hAu : A *ᵥ u = c • v := by
    simp only [u, Matrix.mulVec_mulVec, hA2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hv0 : v ≠ 0 := by simpa using hLI.ne_zero (0 : Fin 2)
  have hpair : ∀ a : K, a • v ≠ u := (LinearIndependent.pair_iff' hv0).mp hLI
  have hW : Submodule.span K ({v, u} : Set (Fin n → K)) < ⊤ := pair_span_lt_top hn v u
  obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hW
  have hfv : f v = 0 := LinearMap.mem_ker.mp (hker (Submodule.subset_span (by simp)))
  have hfu : f u = 0 := LinearMap.mem_ker.mp (hker (Submodule.subset_span (by simp)))
  let ψ : Fin n → K := fun j => f (Pi.single j 1)
  have hψ : ∀ x : Fin n → K, f x = ψ ⬝ᵥ x :=
    fun x => functional_dotProduct f x ψ (fun _ => rfl)
  have hψv : ψ ⬝ᵥ v = 0 := by rw [← hψ v]; exact hfv
  have hψu : ψ ⬝ᵥ u = 0 := by rw [← hψ u]; exact hfu
  let φ : Fin n → K := ψ ᵥ* A
  have hφu : φ ⬝ᵥ u = 0 := by
    simp only [φ]
    rw [← Matrix.dotProduct_mulVec, hAu, dotProduct_smul, hψv, smul_zero]
  have hφv : φ ⬝ᵥ v = 0 := by
    simp only [φ]
    rw [← Matrix.dotProduct_mulVec]
    exact hψu
  have hφA : φ ᵥ* A = c • ψ := by
    simp only [φ, Matrix.vecMul_vecMul, hA2, Matrix.vecMul_smul, Matrix.vecMul_one]
  let N := vecMulVec u ψ - vecMulVec v φ
  refine ⟨N, ?_, ?_, ?_⟩
  · intro hN
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hf
    have hx' : ψ ⬝ᵥ x ≠ 0 := by rwa [hψ x] at hx
    have hNx : N *ᵥ x = (ψ ⬝ᵥ x) • u - (φ ⬝ᵥ x) • v := by
      simp only [N, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec]
      simp
    have hne : N *ᵥ x ≠ 0 := by
      rw [hNx]
      intro h
      have h' : (ψ ⬝ᵥ x) • u = (φ ⬝ᵥ x) • v := sub_eq_zero.mp h
      have h2 : u = ((ψ ⬝ᵥ x)⁻¹ * (φ ⬝ᵥ x)) • v := by
        calc u = (ψ ⬝ᵥ x)⁻¹ • ((ψ ⬝ᵥ x) • u) := by
              rw [smul_smul, inv_mul_cancel₀ hx', one_smul]
          _ = (ψ ⬝ᵥ x)⁻¹ • ((φ ⬝ᵥ x) • v) := by rw [h']
          _ = ((ψ ⬝ᵥ x)⁻¹ * (φ ⬝ᵥ x)) • v := by rw [smul_smul]
      exact hpair _ h2.symm
    rw [hN, Matrix.zero_mulVec] at hne
    exact hne rfl
  · refine ⟨u, v, ψ, -φ, hψu, hψv, ?_, ?_, ?_⟩
    · rw [neg_dotProduct, hφu, neg_zero]
    · rw [neg_dotProduct, hφv, neg_zero]
    · simp only [N, Matrix.vecMulVec_neg, sub_eq_add_neg]
  · have hAN : A * N = c • vecMulVec v ψ - vecMulVec u φ := by
      simp only [N]
      rw [Matrix.mul_sub, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hAu]
      rw [show A *ᵥ v = u from rfl]
      rw [Matrix.smul_vecMulVec]
    have hNA : N * A = vecMulVec u φ - c • vecMulVec v ψ := by
      simp only [N]
      rw [Matrix.sub_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hφA]
      rw [Matrix.vecMulVec_smul]
    rw [hAN, hNA]
    abel

theorem exists_sq_zero_field (hn : 2 ≤ n) {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hσσ : ∀ x, σ (σ x) = x) :
    ∃ N : Matrix (Fin n) (Fin n) K, N ≠ 0 ∧ N * N = 0 ∧ N.map σ = -N := by
  have hy : ∃ y, σ y ≠ y := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  obtain ⟨y, hy⟩ := hy
  let θ := y - σ y
  have hθ : θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hσθ : σ θ = -θ := by
    simp only [θ, map_sub, hσσ]
    ring
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    simp [i, j] at hv
  let N := θ • Matrix.single i j (1 : K)
  refine ⟨N, ?_, ?_, ?_⟩
  · intro h
    have h1 : N i j = 0 := by rw [h, Matrix.zero_apply]
    simp [N, hθ] at h1
  · simp [N, Matrix.single_mul_single_of_ne, Ne.symm hij]
  · ext a b
    simp only [N, Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases h : i = a ∧ j = b
    · simp [h, hσθ]
    · simp [h]

private lemma inv_transpose_neg {A : Matrix (Fin n) (Fin n) K} (hAd : IsUnit A.det)
    (hA : Aᵀ = -A) : (A⁻¹)ᵀ = -A⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, hA]
  have : Invertible (-1 : K) := ⟨-1, by simp, by simp⟩
  have hh := Matrix.inv_smul A (-1 : K) hAd
  simpa using hh

private lemma exists_alt_pair (hn : 3 ≤ n) (B : Matrix (Fin n) (Fin n) K) :
    ∃ (i : Fin n) (w w' : Fin n → K), w = Pi.single i 1 ∧ w' ≠ 0 ∧ w' i = 0 ∧
      (w ᵥ* B) ⬝ᵥ w' = 0 := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  have hij : i ≠ j := by
    intro h; have hv := congrArg Fin.val h; simp [i, j] at hv
  have hik : i ≠ k := by
    intro h; have hv := congrArg Fin.val h; simp [i, k] at hv
  have hjk : j ≠ k := by
    intro h; have hv := congrArg Fin.val h; simp [j, k] at hv
  have hψj : (Pi.single i (1 : K) ᵥ* B) ⬝ᵥ Pi.single j 1 = B i j := by
    rw [Matrix.single_one_vecMul, dotProduct_comm, single_one_dotProduct]
    rfl
  have hψk : (Pi.single i (1 : K) ᵥ* B) ⬝ᵥ Pi.single k 1 = B i k := by
    rw [Matrix.single_one_vecMul, dotProduct_comm, single_one_dotProduct]
    rfl
  by_cases ha : B i j = 0
  · refine ⟨i, Pi.single i 1, Pi.single j 1, rfl, ?_, ?_, ?_⟩
    · intro h
      have hv := congrFun h j
      simp at hv
    · rw [Pi.single_eq_of_ne hij]
    · rw [hψj, ha]
  · let w' : Fin n → K := B i k • Pi.single j 1 - B i j • Pi.single k 1
    have hwk : w' k = - B i j := by
      simp [w', Pi.single_eq_of_ne (Ne.symm hjk), Pi.single_eq_same]
    refine ⟨i, Pi.single i 1, w', rfl, ?_, ?_, ?_⟩
    · intro h
      rw [h] at hwk
      exact ha (neg_eq_zero.mp hwk.symm)
    · simp [w', Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik]
    · simp only [w', dotProduct_sub, dotProduct_smul, hψj, hψk,
        smul_eq_mul]
      ring

theorem exists_rankTwo_alt (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) K}
    (hAd : IsUnit A.det) (hA : Aᵀ = -A) :
    ∃ N : Matrix (Fin n) (Fin n) K, N ≠ 0 ∧ IsRankTwoSqZero N ∧ A * Nᵀ = N * A := by
  classical
  let B := A⁻¹
  have hBt : Bᵀ = -B := by
    simp only [B]
    exact inv_transpose_neg hAd hA
  have hAB : A * B = 1 := Matrix.mul_nonsing_inv A hAd
  have hBA : B * A = 1 := Matrix.nonsing_inv_mul A hAd
  have hanti : ∀ x y : Fin n → K, x ⬝ᵥ (B *ᵥ y) = -(y ⬝ᵥ (B *ᵥ x)) := by
    intro x y
    have h := Matrix.dotProduct_transpose_mulVec B y x
    rw [hBt, Matrix.neg_mulVec, dotProduct_neg] at h
    exact h.symm
  have halt : ∀ x : Fin n → K, x ⬝ᵥ (B *ᵥ x) = 0 := by
    intro x
    have h := hanti x x
    have hzero : (2 : K) * (x ⬝ᵥ (B *ᵥ x)) = 0 := by
      rw [two_mul]
      nth_rewrite 1 [h]
      abel
    exact (mul_eq_zero.mp hzero).resolve_left h2
  obtain ⟨i, w, w', hw, hw'ne, hw'i, hψw'⟩ := exists_alt_pair hn B
  let ψ := w ᵥ* B
  let φ := w' ᵥ* B
  have hψw : ψ ⬝ᵥ w = 0 := by
    simpa [ψ, ← Matrix.dotProduct_mulVec] using halt w
  have hφw : φ ⬝ᵥ w = 0 := by
    have hw'B : w ⬝ᵥ (B *ᵥ w') = 0 := by
      simpa [ψ, ← Matrix.dotProduct_mulVec] using hψw'
    calc φ ⬝ᵥ w = w' ⬝ᵥ (B *ᵥ w) := by
          rw [show φ = w' ᵥ* B from rfl, ← Matrix.dotProduct_mulVec]
      _ = -(w ⬝ᵥ (B *ᵥ w')) := hanti w' w
      _ = 0 := by rw [hw'B, neg_zero]
  have hφw' : φ ⬝ᵥ w' = 0 := by
    simpa [φ, ← Matrix.dotProduct_mulVec] using halt w'
  have hφne : φ ≠ 0 := by
    intro h
    have hw'0 : w' = 0 := by
      calc w' = w' ᵥ* (1 : Matrix (Fin n) (Fin n) K) := by rw [Matrix.vecMul_one]
        _ = w' ᵥ* (B * A) := by rw [hBA]
        _ = (w' ᵥ* B) ᵥ* A := by rw [Matrix.vecMul_vecMul]
        _ = 0 := by rw [show w' ᵥ* B = φ from rfl, h, Matrix.zero_vecMul]
    exact hw'ne hw'0
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hφne
  have hxs : φ ⬝ᵥ Pi.single s 1 ≠ 0 := by
    rw [dotProduct_comm, single_one_dotProduct]
    simpa using hs
  let N := vecMulVec w φ - vecMulVec w' ψ
  have hNx : N *ᵥ Pi.single s 1
      = (φ ⬝ᵥ Pi.single s 1) • w - (ψ ⬝ᵥ Pi.single s 1) • w' := by
    simp only [N, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec]
    simp
  have hcoord : (N *ᵥ Pi.single s 1) i = φ ⬝ᵥ Pi.single s 1 := by
    rw [hNx]
    simp [hw, hw'i]
  refine ⟨N, ?_, ?_, ?_⟩
  · intro hN
    have hne : (N *ᵥ Pi.single s 1) i ≠ 0 := by
      rw [hcoord]
      exact hxs
    rw [hN, Matrix.zero_mulVec] at hne
    exact hne rfl
  · refine ⟨w, w', φ, -ψ, hφw, hφw', ?_, ?_, ?_⟩
    · rw [neg_dotProduct, hψw, neg_zero]
    · rw [neg_dotProduct, hψw', neg_zero]
    · simp only [N, Matrix.vecMulVec_neg, sub_eq_add_neg]
  · have hAφ : A *ᵥ φ = -w' := by
      calc A *ᵥ φ = A *ᵥ (Bᵀ *ᵥ w') := by
            rw [show φ = w' ᵥ* B from rfl, ← Matrix.mulVec_transpose]
        _ = (A * Bᵀ) *ᵥ w' := by rw [Matrix.mulVec_mulVec]
        _ = (A * -B) *ᵥ w' := by rw [hBt]
        _ = (-(A * B)) *ᵥ w' := by rw [Matrix.mul_neg]
        _ = (-(1 : Matrix (Fin n) (Fin n) K)) *ᵥ w' := by rw [hAB]
        _ = -w' := by rw [Matrix.neg_mulVec, Matrix.one_mulVec]
    have hAψ : A *ᵥ ψ = -w := by
      calc A *ᵥ ψ = A *ᵥ (Bᵀ *ᵥ w) := by
            rw [show ψ = w ᵥ* B from rfl, ← Matrix.mulVec_transpose]
        _ = (A * Bᵀ) *ᵥ w := by rw [Matrix.mulVec_mulVec]
        _ = (A * -B) *ᵥ w := by rw [hBt]
        _ = (-(A * B)) *ᵥ w := by rw [Matrix.mul_neg]
        _ = (-(1 : Matrix (Fin n) (Fin n) K)) *ᵥ w := by rw [hAB]
        _ = -w := by rw [Matrix.neg_mulVec, Matrix.one_mulVec]
    have hφA : φ ᵥ* A = w' := by
      calc φ ᵥ* A = (w' ᵥ* B) ᵥ* A := by rw [show φ = w' ᵥ* B from rfl]
        _ = w' ᵥ* (B * A) := by rw [Matrix.vecMul_vecMul]
        _ = w' ᵥ* 1 := by rw [hBA]
        _ = w' := by rw [Matrix.vecMul_one]
    have hψA : ψ ᵥ* A = w := by
      calc ψ ᵥ* A = (w ᵥ* B) ᵥ* A := by rw [show ψ = w ᵥ* B from rfl]
        _ = w ᵥ* (B * A) := by rw [Matrix.vecMul_vecMul]
        _ = w ᵥ* 1 := by rw [hBA]
        _ = w := by rw [Matrix.vecMul_one]
    have hAN : A * Nᵀ = vecMulVec w w' - vecMulVec w' w := by
      simp only [N, Matrix.transpose_sub, Matrix.transpose_vecMulVec]
      rw [Matrix.mul_sub, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hAφ, hAψ,
        Matrix.neg_vecMulVec, Matrix.neg_vecMulVec]
      abel
    have hNA : N * A = vecMulVec w w' - vecMulVec w' w := by
      simp only [N]
      rw [Matrix.sub_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hφA, hψA]
    rw [hAN, hNA]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
