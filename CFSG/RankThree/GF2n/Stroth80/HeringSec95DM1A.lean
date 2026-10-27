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
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.GF2n.Stroth80

namespace HS9

namespace M1

open scoped Matrix MatrixGroups

section Defs

variable {K : Type} [Field K]

@[expose] def smulVec {Y : Type} [AddCommGroup Y] [Module K Y] (g : Matrix (Fin 2) (Fin 2) K)
    (u : Fin 2 → Y) : Fin 2 → Y :=
  fun i => g i 0 • u 0 + g i 1 • u 1

abbrev Wd (K Y₁ Y₂ : Type) [Field K] [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂]
    [Module K Y₂] : Type := (Fin 2 → Y₁) × (Fin 2 → Y₂)

variable {Y₁ Y₂ : Type} [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂] [Module K Y₂]

@[expose] def actW (g h : Matrix (Fin 2) (Fin 2) K) (y : Wd K Y₁ Y₂) : Wd K Y₁ Y₂ :=
  (smulVec g y.1, smulVec h y.2)

@[expose] def formW (β₁ : Y₁ →ₗ[K] Y₁ →ₗ[K] K) (β₂ : Y₂ →ₗ[K] Y₂ →ₗ[K] K) (a a' : Wd K Y₁ Y₂) : K :=
  β₁ (a.1 0) (a'.1 1) + β₁ (a.1 1) (a'.1 0) + β₂ (a.2 0) (a'.2 1) + β₂ (a.2 1) (a'.2 0)

@[expose] def uMat (s : K) : Matrix (Fin 2) (Fin 2) K := !![1, s; 0, 1]

theorem smulVec_one {Y : Type} [AddCommGroup Y] [Module K Y] (u : Fin 2 → Y) :
    smulVec (1 : Matrix (Fin 2) (Fin 2) K) u = u := by
  ext i
  simp only [smulVec, Matrix.one_apply]
  fin_cases i <;> simp

theorem smulVec_zero {Y : Type} [AddCommGroup Y] [Module K Y] (g : Matrix (Fin 2) (Fin 2) K) :
    smulVec g (0 : Fin 2 → Y) = 0 := by
  ext i
  simp [smulVec]

theorem smulVec_add {Y : Type} [AddCommGroup Y] [Module K Y] (g : Matrix (Fin 2) (Fin 2) K)
    (u v : Fin 2 → Y) : smulVec g (u + v) = smulVec g u + smulVec g v := by
  ext i
  simp only [smulVec, Pi.add_apply, smul_add]
  abel

theorem smulVec_mul {Y : Type} [AddCommGroup Y] [Module K Y] (g h : Matrix (Fin 2) (Fin 2) K)
    (u : Fin 2 → Y) : smulVec (g * h) u = smulVec g (smulVec h u) := by
  ext i
  simp only [smulVec, Matrix.mul_apply, Fin.sum_univ_two, add_smul, smul_add, smul_smul]
  abel

theorem uMat_zero : uMat (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

end Defs

section TB

variable {K : Type} [Field K] {Y₁ Y₂ : Type} [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂]
  [Module K Y₂]

theorem uMat_apply_00 (s : K) : uMat s 0 0 = 1 := rfl
theorem uMat_apply_01 (s : K) : uMat s 0 1 = s := rfl
theorem uMat_apply_10 (s : K) : uMat s 1 0 = 0 := rfl
theorem uMat_apply_11 (s : K) : uMat s 1 1 = 1 := rfl

theorem actW_uMat_zero_second (s' : K) (w : Fin 2 → Y₂) :
    actW (uMat (0 : K)) (uMat s') ((0 : Fin 2 → Y₁), w) =
      (0, ![w 0 + s' • w 1, w 1]) := by
  refine Prod.ext ?_ ?_
  · simp [actW, smulVec_zero]
  · ext i
    fin_cases i <;> simp [actW, smulVec, uMat]

theorem eqv_second (θ : Wd K Y₁ Y₂ →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hθ : ∀ (s s' : K) (y : Wd K Y₁ Y₂),
      θ (actW (uMat s) (uMat s') y) = uMat s * θ y * (uMat s')ᵀ) :
    (∀ u : Fin 2 → Y₁, θ (u, 0) 0 1 = 0 ∧ θ (u, 0) 1 1 = 0) ∧
    ∃ a b : Y₂ →ₗ[K] K, ∀ w : Fin 2 → Y₂,
      θ (0, w) = !![a (w 0) + b (w 1), a (w 1); 0, 0] := by
  refine ⟨fun u => ?_, ?_⟩
  · have e : actW (uMat (0 : K)) (uMat 1) (u, (0 : Fin 2 → Y₂)) = (u, 0) := by
      simp [actW, uMat_zero, smulVec_one, smulVec_zero]
    have h := hθ 0 1 (u, 0)
    rw [e, uMat_zero, one_mul] at h
    have h0 := congrFun (congrFun h 0) 0
    have h1 := congrFun (congrFun h 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, uMat] at h0 h1
    exact ⟨h0, h1⟩
  · set T₂ : (Fin 2 → Y₂) →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
      θ ∘ₗ LinearMap.inr K (Fin 2 → Y₁) (Fin 2 → Y₂) with hT₂
    have hT₂apply : ∀ w, T₂ w = θ (0, w) := fun w => rfl
    have hrow : ∀ w j, θ (0, w) 1 j = 0 := by
      intro w j
      have e : actW (uMat (1 : K)) (uMat (0 : K)) ((0 : Fin 2 → Y₁), w) = (0, w) := by
        simp [actW, uMat_zero, smulVec_one, smulVec_zero]
      have h := hθ 1 0 (0, w)
      rw [e, uMat_zero, Matrix.transpose_one, mul_one] at h
      have h0 := congrFun (congrFun h 0) j
      simp [Matrix.mul_apply, Fin.sum_univ_two, uMat] at h0
      exact h0
    have hsplit : ∀ w : Fin 2 → Y₂, w = Pi.single 0 (w 0) + Pi.single 1 (w 1) := by
      intro w
      ext i
      fin_cases i <;> simp
    have hF0 : ∀ y : Y₂, θ (0, Pi.single 0 y) 0 1 = 0 ∧
        θ (0, Pi.single 0 y) 0 0 = θ (0, Pi.single 1 y) 0 1 := by
      intro y
      have e : actW (uMat (0 : K)) (uMat (1 : K)) ((0 : Fin 2 → Y₁), (Pi.single 1 y : Fin 2 → Y₂)) =
          (0, Pi.single 0 y + Pi.single 1 y) := by
        rw [actW_uMat_zero_second]
        refine Prod.ext rfl ?_
        ext i
        fin_cases i <;> simp
      have h := hθ 0 1 (0, Pi.single 1 y)
      rw [e, uMat_zero, one_mul] at h
      have hadd : θ (0, Pi.single 0 y + Pi.single 1 y) =
          θ (0, Pi.single 0 y) + θ (0, Pi.single 1 y) := by
        rw [← map_add]
        simp
      rw [hadd] at h
      have h0 := congrFun (congrFun h 0) 0
      have h1 := congrFun (congrFun h 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, uMat] at h0 h1
      refine ⟨by linear_combination h1, by linear_combination h0⟩
    refine ⟨(Matrix.entryLinearMap K K 0 1) ∘ₗ T₂ ∘ₗ LinearMap.single K (fun _ : Fin 2 => Y₂) 1,
      (Matrix.entryLinearMap K K 0 0) ∘ₗ T₂ ∘ₗ LinearMap.single K (fun _ : Fin 2 => Y₂) 1, ?_⟩
    intro w
    have hw := hsplit w
    have hθw : θ (0, w) = θ (0, Pi.single 0 (w 0)) + θ (0, Pi.single 1 (w 1)) := by
      conv_lhs => rw [hw]
      rw [← map_add]
      simp
    ext i j
    fin_cases i <;> fin_cases j
    · simp [hθw, hT₂apply, (hF0 (w 0)).2]
    · simp [hθw, hT₂apply, (hF0 (w 0)).1]
    · simp [hθw, hrow]
    · simp [hθw, hrow]

theorem eqv_second_11 (θ : Wd K Y₁ Y₂ →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hθ : ∀ (s s' : K) (y : Wd K Y₁ Y₂),
      θ (actW (uMat s) (uMat s') y) = uMat s * θ y * (uMat s')ᵀ) (y : Wd K Y₁ Y₂) :
    θ y 1 1 = 0 := by
  obtain ⟨hcol, a, b, hab⟩ := eqv_second θ hθ
  have hy : y = (y.1, 0) + (0, y.2) := by simp
  rw [hy, map_add, Matrix.add_apply, (hcol y.1).2, hab]
  simp

@[expose] def nilMat (α γ : K) : Matrix (Fin 2) (Fin 2) K := !![α * γ, α ^ 2; γ ^ 2, α * γ]

theorem actW_one_conj_second (N : Matrix (Fin 2) (Fin 2) K) (s' : K) (w : Fin 2 → Y₂) :
    actW (1 : Matrix (Fin 2) (Fin 2) K) (1 + s' • N) ((0 : Fin 2 → Y₁), w) =
      (0, ![w 0 + s' • (N 0 0 • w 0 + N 0 1 • w 1), w 1 + s' • (N 1 0 • w 0 + N 1 1 • w 1)]) := by
  refine Prod.ext ?_ ?_
  · simp [actW, smulVec_one]
  · ext i
    fin_cases i <;> simp [actW, smulVec, Matrix.one_apply, add_smul, smul_smul] <;> abel

theorem actW_one_conj_first (N : Matrix (Fin 2) (Fin 2) K) (s' : K) (u : Fin 2 → Y₁) :
    actW (1 : Matrix (Fin 2) (Fin 2) K) (1 + s' • N) (u, (0 : Fin 2 → Y₂)) = (u, 0) := by
  simp [actW, smulVec_one, smulVec_zero]

theorem eqv_D (θ : Wd K Y₁ Y₂ →ₗ[K] Matrix (Fin 2) (Fin 2) K) (α γ : K) (hγ : γ ≠ 0)
    (hB : ∀ (s s' : K) (y : Wd K Y₁ Y₂),
      θ (actW (uMat s) (uMat s') y) = uMat s * θ y * (uMat s')ᵀ)
    (hC : ∀ (s' : K) (y : Wd K Y₁ Y₂),
      θ (actW 1 (1 + s' • nilMat α γ) y) = θ y * (1 + s' • nilMat α γ)ᵀ) :
    (∀ u : Fin 2 → Y₁, θ (u, 0) = 0) ∧ ∃ a : Y₂ →ₗ[K] K, ∀ w : Fin 2 → Y₂,
      θ (0, w) = !![a (w 0), a (w 1); 0, 0] := by
  obtain ⟨hcol, a, b, hab⟩ := eqv_second θ hB
  refine ⟨fun u => ?_, a, fun w => ?_⟩
  · have h := hC 1 (u, 0)
    rw [actW_one_conj_first] at h
    have h0 := congrFun (congrFun h 0) 1
    have h1 := congrFun (congrFun h 1) 1
    obtain ⟨c01, c11⟩ := hcol u
    simp [Matrix.mul_apply, Fin.sum_univ_two, nilMat, c01, c11] at h0 h1
    ext i j
    fin_cases i <;> fin_cases j
    · exact h0.resolve_right hγ
    · exact c01
    · exact h1.resolve_right hγ
    · exact c11
  · have hb : b = 0 := by
      ext y
      have h := hC 1 (0, ![0, y])
      rw [actW_one_conj_second] at h
      rw [hab, hab] at h
      have h1 := congrFun (congrFun h 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, nilMat, map_add, map_smul] at h1
      have hγ2 : γ ^ 2 ≠ 0 := pow_ne_zero 2 hγ
      have h2 : b y * γ ^ 2 = 0 := by linear_combination -h1
      rcases mul_eq_zero.mp h2 with h | h
      · simpa using h
      · exact absurd h hγ2
    rw [hab, hb]
    simp

@[expose] def pureMap (a : Y₂ →ₗ[K] K) : Wd K Y₁ Y₂ →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun y := !![a (y.2 0), a (y.2 1); 0, 0]
  map_add' y y' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' c y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem pureMap_apply (a : Y₂ →ₗ[K] K) (y : Wd K Y₁ Y₂) :
    pureMap a y = !![a (y.2 0), a (y.2 1); 0, 0] := rfl

theorem pureMap_equiv (a : Y₂ →ₗ[K] K) (h : Matrix (Fin 2) (Fin 2) K) (y : Wd K Y₁ Y₂) :
    pureMap a (actW 1 h y) = pureMap a y * hᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pureMap_apply, actW, smulVec, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

@[expose] def tMat (μ : K) : Matrix (Fin 2) (Fin 2) K := !![μ, 0; 0, μ⁻¹]

theorem actW_add (g h : Matrix (Fin 2) (Fin 2) K) (y y' : Wd K Y₁ Y₂) :
    actW g h (y + y') = actW g h y + actW g h y' := by
  refine Prod.ext ?_ ?_
  · exact smulVec_add g y.1 y'.1
  · exact smulVec_add h y.2 y'.2

section Torus

variable [Fintype K] [DecidableEq K] [CharP K 2]

theorem sum_units_one : ∑ _μ : Kˣ, (1 : K) = 1 := by
  have h := FiniteField.sum_pow_units K 0
  simp only [pow_zero, Units.val_one, dvd_zero, if_true] at h
  rw [h]
  exact CharTwo.neg_eq (1 : K)

theorem sum_units_pow (hq : 4 ≤ Fintype.card K) (i : ℕ) (hi0 : 0 < i) (hi : i < 3) :
    ∑ μ : Kˣ, ((μ : K) ^ i) = 0 := by
  have h := FiniteField.sum_pow_units K i
  have hnd : ¬ (Fintype.card K - 1 ∣ i) := by
    intro hd
    have := Nat.le_of_dvd hi0 hd
    omega
  simpa [hnd] using h

theorem torus_avg (hq : 4 ≤ Fintype.card K) (θ : Wd K Y₁ Y₂ →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hB : ∀ (s s' : K) (y : Wd K Y₁ Y₂),
      θ (actW (uMat s) (uMat s') y) = uMat s * θ y * (uMat s')ᵀ) :
    ∃ a b : Y₂ →ₗ[K] K, (∀ w : Fin 2 → Y₂,
      θ (0, w) = !![a (w 0) + b (w 1), a (w 1); 0, 0]) ∧ ∀ y : Wd K Y₁ Y₂,
      ∑ μ : Kˣ, θ (actW 1 (tMat ((μ⁻¹ : Kˣ) : K)) y) * tMat (μ : K) = pureMap a y := by
  obtain ⟨hcol, a, b, hab⟩ := eqv_second θ hB
  refine ⟨a, b, hab, fun y => ?_⟩
  have hy : y = (y.1, 0) + (0, y.2) := by simp
  have hs1 : ∑ μ : Kˣ, (μ : K) = 0 := by
    have := sum_units_pow (K := K) hq 1 (by norm_num) (by norm_num)
    simpa using this
  have hs2 : ∑ μ : Kˣ, (μ : K) ^ 2 = 0 := sum_units_pow hq 2 (by norm_num) (by norm_num)
  have hinv : ∀ μ : Kˣ, (((μ⁻¹ : Kˣ) : K)) = (μ : K)⁻¹ := fun μ => Units.val_inv_eq_inv_val μ
  have hne : ∀ μ : Kˣ, (μ : K) ≠ 0 := fun μ => μ.ne_zero
  have h1 : ∀ μ : Kˣ, θ (actW 1 (tMat ((μ⁻¹ : Kˣ) : K)) (y.1, 0)) * tMat (μ : K) =
      (μ : K) • θ (y.1, 0) := by
    intro μ
    have e : actW 1 (tMat ((μ⁻¹ : Kˣ) : K)) (y.1, (0 : Fin 2 → Y₂)) = (y.1, 0) := by
      simp [actW, smulVec_one, smulVec_zero]
    rw [e]
    obtain ⟨c01, c11⟩ := hcol y.1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tMat, Matrix.mul_apply, Fin.sum_univ_two, c01, c11, mul_comm]
  have h2 : ∀ μ : Kˣ, θ (actW 1 (tMat ((μ⁻¹ : Kˣ) : K)) (0, y.2)) * tMat (μ : K) =
      !![a (y.2 0) + (μ : K) ^ 2 * b (y.2 1), a (y.2 1); 0, 0] := by
    intro μ
    have e : actW 1 (tMat ((μ⁻¹ : Kˣ) : K)) ((0 : Fin 2 → Y₁), y.2) =
        (0, ![(μ : K)⁻¹ • y.2 0, (μ : K) • y.2 1]) := by
      refine Prod.ext ?_ ?_
      · simp [actW, smulVec_zero]
      · ext i
        fin_cases i <;> simp [actW, smulVec, tMat, hinv]
    rw [e, hab]
    have hne' := hne μ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tMat, Matrix.mul_apply, Fin.sum_univ_two, map_smul, smul_eq_mul] <;> field_simp
  have hsum : ∑ μ : Kˣ, θ (actW 1 (tMat ((μ⁻¹ : Kˣ) : K)) y) * tMat (μ : K) =
      ∑ μ : Kˣ, ((μ : K) • θ (y.1, 0) +
        !![a (y.2 0) + (μ : K) ^ 2 * b (y.2 1), a (y.2 1); 0, 0]) := by
    refine Finset.sum_congr rfl fun μ _ => ?_
    conv_lhs => rw [hy, actW_add, map_add, add_mul]
    rw [h1, h2]
  rw [hsum, Finset.sum_add_distrib, ← Finset.sum_smul, hs1, zero_smul, zero_add]
  have hone := sum_units_one (K := K)
  have hc : ((Fintype.card Kˣ : ℕ) : K) = 1 := by
    simpa [Finset.sum_const, Finset.card_univ] using hone
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sum_apply, pureMap_apply, Finset.sum_add_distrib, ← Finset.sum_mul, hs2, hc]

end Torus

section X2

variable [Module.Finite K Y₂]

theorem exists_eq_of_nondeg (β : Y₂ →ₗ[K] Y₂ →ₗ[K] K) (hnd : ∀ y, (∀ y', β y y' = 0) → y = 0)
    (f : Y₂ →ₗ[K] K) : ∃ y, β y = f := by
  have hinj : Function.Injective β := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hnd y fun y' => by simpa using LinearMap.congr_fun hy y'
  have hdim : Module.finrank K Y₂ = Module.finrank K (Y₂ →ₗ[K] K) :=
    (Subspace.dual_finrank_eq (K := K) (V := Y₂)).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj f

theorem exists_smul_of_ker_le {V : Type} [AddCommGroup V] [Module K V] (f g : V →ₗ[K] K)
    (h : ∀ v, g v = 0 → f v = 0) : ∃ c : K, f = c • g := by
  by_cases hg : g = 0
  · refine ⟨0, ?_⟩
    ext v
    simp [h v (by simp [hg])]
  · obtain ⟨v₀, hv₀⟩ : ∃ v₀, g v₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hg (LinearMap.ext hcon)
    refine ⟨f v₀ / g v₀, ?_⟩
    ext v
    have h1 : g (v - (g v / g v₀) • v₀) = 0 := by
      simp [map_sub, map_smul, hv₀]
    have h2 := h _ h1
    simp only [map_sub, map_smul, smul_eq_mul] at h2
    simp only [LinearMap.smul_apply, smul_eq_mul]
    have h3 : f v = g v / g v₀ * f v₀ := by linear_combination h2
    rw [h3]
    field_simp

theorem X2_form (β₁ : Y₁ →ₗ[K] Y₁ →ₗ[K] K) (β₂ : Y₂ →ₗ[K] Y₂ →ₗ[K] K)
    (hnd₁ : ∀ y, (∀ y', β₁ y y' = 0) → y = 0) (hnd₂ : ∀ y, (∀ y', β₂ y y' = 0) → y = 0)
    (aₜ : Y₂ →ₗ[K] K) (X₂ : Set (Wd K Y₁ Y₂))
    (hort : ∀ x ∈ X₂, ∀ x' : Wd K Y₁ Y₂, pureMap aₜ x' = 0 → formW β₁ β₂ x x' = 0) :
    ∃ y : Y₂, ∀ x ∈ X₂, x.1 = 0 ∧ ∃ c₀ c₁ : K, x.2 = ![c₀ • y, c₁ • y] := by
  obtain ⟨yₜ, hyₜ⟩ := exists_eq_of_nondeg β₂ hnd₂ aₜ
  refine ⟨yₜ, fun x hx => ?_⟩
  have hz : ∀ (u' : Fin 2 → Y₁), pureMap aₜ (u', (0 : Fin 2 → Y₂)) = 0 := by
    intro u'
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pureMap_apply]
  have hu : x.1 = 0 := by
    have h0 : ∀ v : Y₁, β₁ (x.1 0) v = 0 := by
      intro v
      have := hort x hx (![0, v], 0) (hz _)
      simpa [formW] using this
    have h1 : ∀ v : Y₁, β₁ (x.1 1) v = 0 := by
      intro v
      have := hort x hx (![v, 0], 0) (hz _)
      simpa [formW] using this
    ext i
    fin_cases i
    · exact hnd₁ _ h0
    · exact hnd₁ _ h1
  refine ⟨hu, ?_⟩
  have hker : ∀ (w' : Fin 2 → Y₂), aₜ (w' 0) = 0 → aₜ (w' 1) = 0 →
      pureMap aₜ ((0 : Fin 2 → Y₁), w') = 0 := by
    intro w' h0 h1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pureMap_apply, h0, h1]
  have hw : ∀ i : Fin 2, ∃ c : K, x.2 i = c • yₜ := by
    intro i
    have hv : ∀ v, aₜ v = 0 → β₂ (x.2 i) v = 0 := by
      intro v hv
      fin_cases i
      · have := hort x hx (0, ![0, v]) (hker _ (by simp) (by simpa using hv))
        simpa [formW] using this
      · have := hort x hx (0, ![v, 0]) (hker _ (by simpa using hv) (by simp))
        simpa [formW] using this
    obtain ⟨c, hc⟩ := exists_smul_of_ker_le (β₂ (x.2 i)) aₜ hv
    refine ⟨c, ?_⟩
    have : β₂ (x.2 i - c • yₜ) = 0 := by
      rw [map_sub, map_smul, hyₜ, hc, sub_self]
    have h4 := hnd₂ (x.2 i - c • yₜ) fun y' => by
      have h5 := LinearMap.congr_fun this y'
      simpa using h5
    exact sub_eq_zero.mp h4
  obtain ⟨c₀, h0⟩ := hw 0
  obtain ⟨c₁, h1⟩ := hw 1
  refine ⟨c₀, c₁, ?_⟩
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

theorem pure_ne_zero (β₁ : Y₁ →ₗ[K] Y₁ →ₗ[K] K) (β₂ : Y₂ →ₗ[K] Y₂ →ₗ[K] K)
    (hnd₁ : ∀ y, (∀ y', β₁ y y' = 0) → y = 0) (hnd₂ : ∀ y, (∀ y', β₂ y y' = 0) → y = 0)
    (aₜ : Y₂ →ₗ[K] K) (X₂ : Set (Wd K Y₁ Y₂))
    (hort : ∀ x ∈ X₂, ∀ x' : Wd K Y₁ Y₂, pureMap aₜ x' = 0 → formW β₁ β₂ x x' = 0)
    (a b : Y₂ →ₗ[K] K) (θₓ : Wd K Y₁ Y₂ →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hθ : ∀ w : Fin 2 → Y₂, θₓ (0, w) = !![a (w 0) + b (w 1), a (w 1); 0, 0])
    (hP : ∃ x₁ ∈ X₂, θₓ x₁ = !![(0 : K), 1; 0, 0]) :
    ∃ x₂ ∈ X₂, pureMap a x₂ ≠ 0 := by
  obtain ⟨y, hy⟩ := X2_form β₁ β₂ hnd₁ hnd₂ aₜ X₂ hort
  obtain ⟨x₁, hx₁, hθx₁⟩ := hP
  obtain ⟨hu, c₀, c₁, hw⟩ := hy x₁ hx₁
  have hx : x₁ = (0, ![c₀ • y, c₁ • y]) := Prod.ext hu hw
  refine ⟨x₁, hx₁, fun h0 => ?_⟩
  rw [hx, hθ] at hθx₁
  have e1 := congrFun (congrFun hθx₁ 0) 1
  have e2 := congrFun (congrFun h0 0) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at e1
  have e2' : a (c₁ • y) = 0 := by
    have h3 : (pureMap a) x₁ 0 1 = a (x₁.2 1) := by simp [pureMap_apply]
    rw [h3, hw] at e2
    simpa using e2
  rw [e2'] at e1
  exact zero_ne_one e1

end X2

end TB
section Extras

variable {K : Type} [Field K]

theorem uMat_mul (s s' : K) : uMat s * uMat s' = uMat (s + s') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[expose] def uSL (s : K) : SL(2, K) :=
  ⟨uMat s, by simp [uMat, Matrix.det_fin_two]⟩

@[expose] def lMat (s : K) : Matrix (Fin 2) (Fin 2) K := !![1, 0; s, 1]

@[expose] def lSL (s : K) : SL(2, K) :=
  ⟨lMat s, by simp [lMat, Matrix.det_fin_two]⟩

theorem coe_uSL (s : K) : ((uSL s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = uMat s := rfl

theorem coe_lSL (s : K) : ((lSL s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = lMat s := rfl

@[expose] def tSL (μ : Kˣ) : SL(2, K) :=
  ⟨tMat (μ : K), by simp [tMat, Matrix.det_fin_two]⟩

theorem coe_tSL (μ : Kˣ) : ((tSL μ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = tMat (μ : K) := rfl

theorem tMat_mul_inv (μ : Kˣ) : tMat (μ : K) * tMat (((μ⁻¹ : Kˣ) : K)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem tMat_transpose (μ : K) : (tMat μ)ᵀ = tMat μ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat]

theorem tMat_unit_smul (μ : Kˣ) :
    Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K) * (tMat (μ : K))ᵀ =
      (μ : K) • Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K) := by
  rw [tMat_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tMat, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.single_apply]

theorem exists_uMat_of_fix [CharP K 2] (g h : SL(2, K))
    (hE : (g : Matrix (Fin 2) (Fin 2) K) * Matrix.single 0 0 1 * (h : Matrix (Fin 2) (Fin 2) K)ᵀ =
      Matrix.single 0 0 1)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) * g = 1) :
    ∃ s s' : K, (g : Matrix (Fin 2) (Fin 2) K) = uMat s ∧
      (h : Matrix (Fin 2) (Fin 2) K) = uMat s' := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have dg := g.det_coe
  have dh := h.det_coe
  rw [Matrix.det_fin_two] at dg dh
  have e00 := congrFun (congrFun hE 0) 0
  have e01 := congrFun (congrFun hE 0) 1
  have e10 := congrFun (congrFun hE 1) 0
  have g00 := congrFun (congrFun hg 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply] at e00 e01 e10 g00
  have hg00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at e00
    exact zero_ne_one e00
  have hh00 : (h : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at e00
    exact zero_ne_one e00
  have hg10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := e10.resolve_right hh00
  have hh10 : (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := e01.resolve_left hg00
  rw [hg10] at dg g00
  have hsq : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    linear_combination g00
  have hone : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have h3 : ((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hsq + (1 - (g : Matrix (Fin 2) (Fin 2) K) 0 0) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h3)
  have hg11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [hone] at dg
    linear_combination dg
  have hh00' : (h : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    rw [hone] at e00
    linear_combination e00
  have hh11 : (h : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [hh00', hh10] at dh
    linear_combination dh
  refine ⟨(g : Matrix (Fin 2) (Fin 2) K) 0 1, (h : Matrix (Fin 2) (Fin 2) K) 0 1, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [uMat, hone, hg10, hg11]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [uMat, hh00', hh10, hh11]

theorem conj_uMat [CharP K 2] (h : SL(2, K)) (s : K) :
    (h : Matrix (Fin 2) (Fin 2) K) * uMat s * ((h⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      1 + s • nilMat ((h : Matrix (Fin 2) (Fin 2) K) 0 0) ((h : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have dh := h.det_coe
  rw [Matrix.det_fin_two] at dh
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, nilMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · linear_combination dh - (s * (h : Matrix (Fin 2) (Fin 2) K) 0 0 *
      (h : Matrix (Fin 2) (Fin 2) K) 1 0) * h2
  · ring
  · linear_combination (-(((h : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 * s)) * h2
  · linear_combination dh

end Extras

section Extras2

variable {K : Type} [Field K] {Y₁ Y₂ : Type} [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂]
  [Module K Y₂]

theorem eq_one_of_act_eq_self [CharP K 2] (g h : SL(2, K))
    (hX : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K) * X * (h : Matrix (Fin 2) (Fin 2) K)ᵀ = X) :
    g = 1 ∧ h = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have dg := g.det_coe
  rw [Matrix.det_fin_two] at dg
  have key : ∀ a b i j : Fin 2, (g : Matrix (Fin 2) (Fin 2) K) i a *
      (h : Matrix (Fin 2) (Fin 2) K) j b = if a = i ∧ b = j then 1 else 0 := by
    intro a b i j
    have := congrFun (congrFun (hX (Matrix.single a b 1)) i) j
    fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply] using this
  have k0000 := key 0 0 0 0
  have k0010 := key 0 0 1 0
  have k0001 := key 0 0 0 1
  have k1101 := key 1 1 0 1
  have k1111 := key 1 1 1 1
  have k1110 := key 1 1 1 0
  have k0101 := key 0 1 0 1
  have k1010 := key 1 0 1 0
  simp at k0000 k0010 k0001 k1101 k1111 k1110 k0101 k1010
  have hg00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at k0000
    exact zero_ne_one k0000
  have hh00 : (h : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at k0000
    exact zero_ne_one k0000
  have hg11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at k1111
    exact zero_ne_one k1111
  have hh11 : (h : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at k1111
    exact zero_ne_one k1111
  have hg10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := k0010.resolve_right hh00
  have hh10 : (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := k0001.resolve_left hg00
  have hg01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := k1101.resolve_right hh11
  have hh01 : (h : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := k1110.resolve_left hg11
  have hgg : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = (g : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have : ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - (g : Matrix (Fin 2) (Fin 2) K) 0 0) *
        (h : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := by linear_combination k1010 - k0000
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hh00)
  rw [hg10, hg01, hgg] at dg
  have hsq : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    linear_combination dg
  have hone : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have h3 : ((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hsq + (1 - (g : Matrix (Fin 2) (Fin 2) K) 0 0) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h3)
  have hh00' : (h : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    rw [hone] at k0000
    linear_combination k0000
  have hh11' : (h : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [hone] at k0101
    linear_combination k0101
  constructor
  · refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hg10, hg01, hgg, hone]
  · refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hh10, hh01, hh00', hh11']

theorem eqv_all_zero (f : Wd K Y₁ Y₂ →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hf : ∀ (g h : SL(2, K)) (y : Wd K Y₁ Y₂),
      f (actW (g : Matrix (Fin 2) (Fin 2) K) (h : Matrix (Fin 2) (Fin 2) K) y) =
        (g : Matrix (Fin 2) (Fin 2) K) * f y * (h : Matrix (Fin 2) (Fin 2) K)ᵀ) : f = 0 := by
  have hfirst : ∀ u : Fin 2 → Y₁, f (u, 0) = 0 := by
    intro u
    have e : ∀ h : Matrix (Fin 2) (Fin 2) K,
        actW (1 : Matrix (Fin 2) (Fin 2) K) h (u, (0 : Fin 2 → Y₂)) = (u, 0) := by
      intro h
      simp [actW, smulVec_one, smulVec_zero]
    have h1 := hf 1 (uSL 1) (u, 0)
    have h2 := hf 1 (lSL 1) (u, 0)
    rw [Matrix.SpecialLinearGroup.coe_one, coe_uSL, e, one_mul] at h1
    rw [Matrix.SpecialLinearGroup.coe_one, coe_lSL, e, one_mul] at h2
    have a1 := congrFun (congrFun h1 0) 0
    have a2 := congrFun (congrFun h1 1) 0
    have a3 := congrFun (congrFun h2 0) 1
    have a4 := congrFun (congrFun h2 1) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two] at a1 a2 a3 a4
    simp [uMat, lMat] at a1 a2 a3 a4
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using a3
    · simpa using a1
    · simpa using a4
    · simpa using a2
  have hsecond : ∀ w : Fin 2 → Y₂, f (0, w) = 0 := by
    intro w
    have e : ∀ g : Matrix (Fin 2) (Fin 2) K,
        actW g (1 : Matrix (Fin 2) (Fin 2) K) ((0 : Fin 2 → Y₁), w) = (0, w) := by
      intro g
      simp [actW, smulVec_one, smulVec_zero]
    have h1 := hf (uSL 1) 1 (0, w)
    have h2 := hf (lSL 1) 1 (0, w)
    rw [Matrix.SpecialLinearGroup.coe_one, coe_uSL, e, Matrix.transpose_one, mul_one] at h1
    rw [Matrix.SpecialLinearGroup.coe_one, coe_lSL, e, Matrix.transpose_one, mul_one] at h2
    have a1 := congrFun (congrFun h1 0) 0
    have a2 := congrFun (congrFun h1 0) 1
    have a3 := congrFun (congrFun h2 1) 0
    have a4 := congrFun (congrFun h2 1) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two] at a1 a2 a3 a4
    simp [uMat, lMat] at a1 a2 a3 a4
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using a3
    · simpa using a4
    · simpa using a1
    · simpa using a2
  refine LinearMap.ext fun y => ?_
  have hy : y = (y.1, 0) + (0, y.2) := by simp
  rw [hy, map_add, hfirst, hsecond]
  simp

end Extras2

end M1

end HS9

end CFSG.RankThree.GF2n.Stroth80
