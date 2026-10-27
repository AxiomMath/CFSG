module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open Matrix

variable {K : Type} [Field K]

@[expose] def sl2Diag (c : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem det_sub_smul_one_fin_two (M : Matrix (Fin 2) (Fin 2) K) (c : K) :
    (M - c • (1 : Matrix (Fin 2) (Fin 2) K)).det =
      (M 0 0 - c) * (M 1 1 - c) - M 0 1 * M 1 0 := by
  rw [Matrix.det_fin_two]
  simp [Matrix.one_apply]

theorem eigen_equation_components (M : Matrix (Fin 2) (Fin 2) K) (c : K) (v : Fin 2 → K)
    (hv : (M - c • (1 : Matrix (Fin 2) (Fin 2) K)) *ᵥ v = 0) :
    M 0 0 * v 0 + M 0 1 * v 1 = c * v 0 ∧ M 1 0 * v 0 + M 1 1 * v 1 = c * v 1 := by
  constructor
  · have h := congrFun hv 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] at h
    linear_combination h
  · have h := congrFun hv 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] at h
    linear_combination h

theorem exists_eigenvalue_of_pow_card [Finite K] (M : Matrix (Fin 2) (Fin 2) K)
    (hpow : M ^ Nat.card K = M) :
    ∃ a : K, (M - a • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hpoly : (∏ c : K, (Polynomial.X - Polynomial.C c : Polynomial K)) =
      Polynomial.X ^ Fintype.card K - Polynomial.X := by
    have hmon : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic :=
      Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hcard1)
    have hnat : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).natDegree =
        Fintype.card K :=
      FiniteField.X_pow_card_sub_X_natDegree_eq K hcard1
    have hroots := FiniteField.roots_X_pow_card_sub_X K
    have hcard : Multiset.card
        (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).roots =
        (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).natDegree := by
      rw [hroots, hnat]
      exact Finset.card_univ
    have key := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard
    rw [hroots] at key
    rw [← key]
    rfl
  rw [Nat.card_eq_fintype_card] at hpow
  let D : Polynomial K →* K :=
    (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) K →* K).comp (Polynomial.aeval M).toMonoidHom
  have hD : ∀ p : Polynomial K, D p = (Polynomial.aeval M p).det := fun p => rfl
  have hL : D (Polynomial.X ^ Fintype.card K - Polynomial.X) = 0 := by
    rw [hD, map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self, Matrix.det_zero]
  have hR : ∀ c : K,
      D (Polynomial.X - Polynomial.C c) = (M - c • (1 : Matrix (Fin 2) (Fin 2) K)).det := by
    intro c
    rw [hD, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  have h : D (∏ c : K, (Polynomial.X - Polynomial.C c : Polynomial K)) =
      ∏ c : K, D (Polynomial.X - Polynomial.C c : Polynomial K) := map_prod D _ _
  rw [hpoly, hL] at h
  simp only [hR] at h
  obtain ⟨c, _, hc⟩ := Finset.prod_eq_zero_iff.mp h.symm
  exact ⟨c, hc⟩

theorem exists_conj_diag_of_eigenvalues (M : Matrix (Fin 2) (Fin 2) K) {a b : K} (hab : a ≠ b)
    (ha : (M - a • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0)
    (hb : (M - b • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0) :
    ∃ Q : Matrix (Fin 2) (Fin 2) K, Q.det = 1 ∧ M * Q = Q * !![a, 0; 0, b] := by
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ha
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hb
  obtain ⟨Ex0, Ex1⟩ := eigen_equation_components M a x hx
  obtain ⟨Ey0, Ey1⟩ := eigen_equation_components M b y hy
  have hxne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra hcon
    simp only [not_or, ne_eq, not_not] at hcon
    apply hx0
    funext i
    fin_cases i <;> simp [hcon.1, hcon.2]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hδ : x 0 * y 1 - y 0 * x 1 ≠ 0 := by
    intro hδ
    have G00 : x 0 * (b - a) * y 0 = 0 := by
      linear_combination M 0 1 * hδ - x 0 * Ey0 + y 0 * Ex0
    have G01 : x 0 * (b - a) * y 1 = 0 := by
      linear_combination (M 1 1 - a) * hδ - x 0 * Ey1 + y 0 * Ex1
    have G10 : x 1 * (b - a) * y 0 = 0 := by
      linear_combination (-(M 0 0 - a)) * hδ - x 1 * Ey0 + y 1 * Ex0
    have G11 : x 1 * (b - a) * y 1 = 0 := by
      linear_combination (-(M 1 0)) * hδ - x 1 * Ey1 + y 1 * Ex1
    have hy' : y 0 = 0 ∧ y 1 = 0 := by
      rcases hxne with h | h
      · exact ⟨(mul_eq_zero.mp G00).resolve_left (mul_ne_zero h hba),
          (mul_eq_zero.mp G01).resolve_left (mul_ne_zero h hba)⟩
      · exact ⟨(mul_eq_zero.mp G10).resolve_left (mul_ne_zero h hba),
          (mul_eq_zero.mp G11).resolve_left (mul_ne_zero h hba)⟩
    apply hy0
    funext i
    fin_cases i <;> simp [hy'.1, hy'.2]
  have hdetQ : (x 0 * y 1 - y 0 * x 1)⁻¹ * (x 0 * y 1 - y 0 * x 1) = 1 :=
    inv_mul_cancel₀ hδ
  refine ⟨!![(x 0 * y 1 - y 0 * x 1)⁻¹ * x 0, y 0; (x 0 * y 1 - y 0 * x 1)⁻¹ * x 1, y 1],
    ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdetQ
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (x 0 * y 1 - y 0 * x 1)⁻¹ * Ex0
    · linear_combination Ey0
    · linear_combination (x 0 * y 1 - y 0 * x 1)⁻¹ * Ex1
    · linear_combination Ey1

theorem orderOf_conj_eq_orderOf {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulEquiv.injective _) x

theorem sl2_conj_diag [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {m : Matrix.SpecialLinearGroup (Fin 2) K} (hord : orderOf m = Nat.card K - 1) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K) (c : Kˣ), orderOf c = Nat.card K - 1 ∧
      g * m * g⁻¹ = sl2Diag c := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hpow : (m : Matrix (Fin 2) (Fin 2) K) ^ (Nat.card K - 1) = 1 := by
    have h := pow_orderOf_eq_one m
    rw [hord] at h
    have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K)) h
    simpa using h'
  have hdet : (m : Matrix (Fin 2) (Fin 2) K) 0 0 * (m : Matrix (Fin 2) (Fin 2) K) 1 1
      - (m : Matrix (Fin 2) (Fin 2) K) 0 1 * (m : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe m
    rw [Matrix.det_fin_two] at h
    exact h
  have hpowq : (m : Matrix (Fin 2) (Fin 2) K) ^ Nat.card K = (m : Matrix (Fin 2) (Fin 2) K) := by
    have hq1 : Nat.card K - 1 + 1 = Nat.card K := by omega
    rw [← hq1, pow_succ, hpow, one_mul]
  set M : Matrix (Fin 2) (Fin 2) K := (m : Matrix (Fin 2) (Fin 2) K) with hM
  have hτ : M 0 0 + M 1 1 ≠ 0 := by
    intro hτ0
    have hMM : M * M = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      · linear_combination (-1 : K) * hdet + M 0 0 * hτ0 - h2
      · linear_combination M 0 1 * hτ0
      · linear_combination M 1 0 * hτ0
      · linear_combination (-1 : K) * hdet + M 1 1 * hτ0 - h2
    have hm2 : m ^ 2 = 1 := by
      rw [pow_two]
      apply Subtype.ext
      exact hMM
    have hdvd : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one hm2
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨a, ha⟩ := exists_eigenvalue_of_pow_card M hpowq
  have ha' : (M 0 0 - a) * (M 1 1 - a) - M 0 1 * M 1 0 = 0 := by
    rw [← det_sub_smul_one_fin_two]
    exact ha
  have hb : (M - (a + (M 0 0 + M 1 1)) • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 := by
    rw [det_sub_smul_one_fin_two]
    linear_combination ha' + a * (M 0 0 + M 1 1) * h2
  have hab : a ≠ a + (M 0 0 + M 1 1) := by
    intro h
    apply hτ
    linear_combination -h
  have hab1 : a * (a + (M 0 0 + M 1 1)) = 1 := by
    linear_combination ha' - hdet + (a * (M 0 0 + M 1 1) - 1) * h2
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hab1
    exact zero_ne_one hab1
  obtain ⟨Q, hQdet, hMQ⟩ := exists_conj_diag_of_eigenvalues M hab ha hb
  obtain ⟨c, hc1⟩ : ∃ c : Kˣ, (c : K) = a := ⟨Units.mk0 a ha0, Units.val_mk0 ha0⟩
  have hc2 : ((c⁻¹ : Kˣ) : K) = a + (M 0 0 + M 1 1) := by
    rw [Units.val_inv_eq_inv_val, hc1]
    exact inv_eq_of_mul_eq_one_right hab1
  have hAdj : Matrix.adjugate Q * M * Q = !![a, 0; 0, a + (M 0 0 + M 1 1)] := by
    calc Matrix.adjugate Q * M * Q = Matrix.adjugate Q * (M * Q) := by rw [Matrix.mul_assoc]
      _ = Matrix.adjugate Q * (Q * !![a, 0; 0, a + (M 0 0 + M 1 1)]) := by rw [hMQ]
      _ = (Matrix.adjugate Q * Q) * !![a, 0; 0, a + (M 0 0 + M 1 1)] := by
          rw [Matrix.mul_assoc]
      _ = !![a, 0; 0, a + (M 0 0 + M 1 1)] := by
          rw [Matrix.adjugate_mul, hQdet, one_smul, one_mul]
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : Matrix.SpecialLinearGroup (Fin 2) K,
      (g₀ : Matrix (Fin 2) (Fin 2) K) = Q := ⟨⟨Q, hQdet⟩, rfl⟩
  have hconj : g₀⁻¹ * m * g₀⁻¹⁻¹ = sl2Diag c := by
    rw [inv_inv]
    apply Subtype.ext
    show Matrix.adjugate (g₀ : Matrix (Fin 2) (Fin 2) K) * M * (g₀ : Matrix (Fin 2) (Fin 2) K) =
      (sl2Diag c : Matrix (Fin 2) (Fin 2) K)
    rw [hg₀, hAdj]
    show !![a, 0; 0, a + (M 0 0 + M 1 1)] = !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)]
    rw [hc1, hc2]
  refine ⟨g₀⁻¹, c, ?_, hconj⟩
  have hmul : ∀ d e : Kˣ, sl2Diag (d * e) = sl2Diag d * sl2Diag e := by
    intro d e
    apply Subtype.ext
    show !![((d * e : Kˣ) : K), 0; 0, (((d * e)⁻¹ : Kˣ) : K)] =
      !![(d : K), 0; 0, ((d⁻¹ : Kˣ) : K)] * !![(e : K), 0; 0, ((e⁻¹ : Kˣ) : K)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv] <;> ring
  have hinj : Function.Injective (MonoidHom.mk' sl2Diag hmul) := by
    intro d e h
    have h' : sl2Diag d = sl2Diag e := h
    have h00 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 0) h'
    exact Units.ext (by simpa [sl2Diag] using h00)
  have hφ : orderOf c = orderOf (sl2Diag c) :=
    (orderOf_injective (MonoidHom.mk' sl2Diag hmul) hinj c).symm
  have hconjord : orderOf (sl2Diag c) = orderOf m := by
    rw [← hconj, orderOf_conj_eq_orderOf]
  rw [hφ, hconjord, hord]

end CFSG.RankThree.GF2n.Smith81.E7Model
