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

namespace CFSG.Sporadic.Co1.Module.CoTwo

open Matrix

variable {K : Type*} [Field K] {ι : Type*} {n : ℕ}

@[expose] def IsInv (M : ι → Matrix (Fin n) (Fin n) K) (U : Submodule K (Fin n → K)) : Prop :=
  ∀ i, ∀ x ∈ U, M i *ᵥ x ∈ U

@[expose] def polyMat (M : ι → Matrix (Fin n) (Fin n) K) (theta : List (List ι)) :
    Matrix (Fin n) (Fin n) K :=
  (theta.map fun w => (w.map M).prod).sum

theorem prod_mulVec_mem {M : ι → Matrix (Fin n) (Fin n) K} {U : Submodule K (Fin n → K)}
    (hU : IsInv M U) (w : List ι) {x : Fin n → K} (hx : x ∈ U) : (w.map M).prod *ᵥ x ∈ U := by
  induction w with
  | nil => simpa using hx
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
    exact hU i _ ih

theorem polyMat_mulVec_mem {M : ι → Matrix (Fin n) (Fin n) K} {U : Submodule K (Fin n → K)}
    (hU : IsInv M U) (theta : List (List ι)) {x : Fin n → K} (hx : x ∈ U) :
    polyMat M theta *ᵥ x ∈ U := by
  unfold polyMat
  induction theta with
  | nil => simp
  | cons w theta ih =>
    rw [List.map_cons, List.sum_cons, Matrix.add_mulVec]
    exact U.add_mem (prod_mulVec_mem hU w hx) ih

structure IsSpin (M : ι → Matrix (Fin n) (Fin n) K) (v : Fin n → K) (u : ℕ → Fin n → K)
    (par : ℕ → ℕ) (lab : ℕ → ι) : Prop where
  root : u 0 = v
  step : ∀ k, 0 < k → k < n → par k < k ∧ u k = M (lab k) *ᵥ u (par k)

theorem IsSpin.mem {M : ι → Matrix (Fin n) (Fin n) K} {v : Fin n → K} {u : ℕ → Fin n → K}
    {par : ℕ → ℕ} {lab : ℕ → ι} (hs : IsSpin M v u par lab) {U : Submodule K (Fin n → K)}
    (hU : IsInv M U) (hv : v ∈ U) : ∀ k, k < n → u k ∈ U := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [hs.root]
      exact hv
    · obtain ⟨hp, he⟩ := hs.step k hpos hk
      rw [he]
      exact hU _ _ (ih _ hp (lt_trans hp hk))

@[expose] def colsMat (u : ℕ → Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i k => u k.val i

theorem eq_top_of_columns {U : Submodule K (Fin n → K)} {A B : Matrix (Fin n) (Fin n) K}
    (hBA : B * A = 1) (hU : ∀ k, (fun i => A i k) ∈ U) : U = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hAB : A * B = 1 := mul_eq_one_comm.1 hBA
  have hx : x = A *ᵥ (B *ᵥ x) := by rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  have hsum : A *ᵥ (B *ᵥ x) = ∑ k, (B *ᵥ x) k • (fun i => A i k) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hx, hsum]
  exact U.sum_mem fun k _ => U.smul_mem _ (hU k)

theorem eq_top_of_spin {M : ι → Matrix (Fin n) (Fin n) K} {v : Fin n → K} {u : ℕ → Fin n → K}
    {par : ℕ → ℕ} {lab : ℕ → ι} (hs : IsSpin M v u par lab) {Vi : Matrix (Fin n) (Fin n) K}
    (hVi : Vi * colsMat u = 1) {U : Submodule K (Fin n → K)} (hU : IsInv M U) (hv : v ∈ U) :
    U = ⊤ :=
  eq_top_of_columns hVi fun k => hs.mem hU hv k.val k.isLt

@[expose] def dotPerp (U : Submodule K (Fin n → K)) : Submodule K (Fin n → K) where
  carrier := {y | ∀ x ∈ U, y ⬝ᵥ x = 0}
  add_mem' := fun {a b} ha hb x hx => by rw [add_dotProduct, ha x hx, hb x hx, add_zero]
  zero_mem' := fun x _ => zero_dotProduct x
  smul_mem' := fun c y hy x hx => by rw [smul_dotProduct, hy x hx, smul_zero]

theorem isInv_transpose_dotPerp {M : ι → Matrix (Fin n) (Fin n) K} {U : Submodule K (Fin n → K)}
    (hU : IsInv M U) : IsInv (fun i => (M i)ᵀ) (dotPerp U) := by
  intro i y hy x hx
  show (M i)ᵀ *ᵥ y ⬝ᵥ x = 0
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  exact hy _ (hU i x hx)

section Kernel

variable {P P' Q Q' Θ : Matrix (Fin n) (Fin n) K} {ℓ : Fin n}

@[expose] def diagOne (ℓ : Fin n) : Matrix (Fin n) (Fin n) K :=
  diagonal fun i => if i = ℓ then 0 else 1

theorem eq_smul_single_of_diagOne_mulVec {z : Fin n → K} (h : diagOne ℓ *ᵥ z = 0) :
    z = z ℓ • Pi.single ℓ 1 := by
  funext i
  by_cases hi : i = ℓ
  · subst hi
    simp
  · have := congrFun h i
    simp only [diagOne, Matrix.mulVec_diagonal, hi, ↓reduceIte, one_mul, Pi.zero_apply] at this
    simp [hi, this]

theorem eq_smul_single_of_vecMul_diagOne {z : Fin n → K} (h : z ᵥ* diagOne ℓ = 0) :
    z = z ℓ • Pi.single ℓ 1 := by
  funext i
  by_cases hi : i = ℓ
  · subst hi
    simp
  · have := congrFun h i
    simp only [diagOne, Matrix.vecMul_diagonal, hi, ↓reduceIte, mul_one, Pi.zero_apply] at this
    simp [hi, this]

theorem eq_smul_of_mulVec_eq_zero (hPP : P * P' = 1) (hD : Q * Θ * P = diagOne ℓ) {x : Fin n → K}
    (hx : Θ *ᵥ x = 0) : x = (P' *ᵥ x) ℓ • (P *ᵥ Pi.single ℓ 1) := by
  have hxz : x = P *ᵥ (P' *ᵥ x) := by rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  have hD0 : diagOne ℓ *ᵥ (P' *ᵥ x) = 0 := by
    rw [← hD, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hxz, hx, Matrix.mulVec_zero]
  have hz := eq_smul_single_of_diagOne_mulVec hD0
  conv_lhs => rw [hxz, hz]
  rw [Matrix.mulVec_smul]

theorem eq_smul_of_vecMul_eq_zero (hQQ : Q * Q' = 1) (hD : Q * Θ * P = diagOne ℓ)
    {y : Fin n → K} (hy : y ᵥ* Θ = 0) : y = (y ᵥ* Q') ℓ • Q ℓ := by
  have hQ'Q : Q' * Q = 1 := mul_eq_one_comm.1 hQQ
  have hyz : y = (y ᵥ* Q') ᵥ* Q := by rw [Matrix.vecMul_vecMul, hQ'Q, Matrix.vecMul_one]
  have hD0 : (y ᵥ* Q') ᵥ* diagOne ℓ = 0 := by
    rw [← hD, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← hyz, hy, Matrix.zero_vecMul]
  have hz := eq_smul_single_of_vecMul_diagOne hD0
  conv_lhs => rw [hyz, hz]
  rw [Matrix.smul_vecMul, Matrix.single_one_vecMul]
  rfl

theorem mulVec_eq_zero_of_diag (hQQ : Q * Q' = 1) (hD : Q * Θ * P = diagOne ℓ) :
    Θ *ᵥ (P *ᵥ Pi.single ℓ 1) = 0 := by
  have hQ'Q : Q' * Q = 1 := mul_eq_one_comm.1 hQQ
  have h1 : Q *ᵥ (Θ *ᵥ (P *ᵥ Pi.single ℓ 1)) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD]
    funext i
    simp [diagOne, Matrix.mulVec_diagonal, Pi.single_apply]
  calc Θ *ᵥ (P *ᵥ Pi.single ℓ 1) = (Q' * Q) *ᵥ (Θ *ᵥ (P *ᵥ Pi.single ℓ 1)) := by
        rw [hQ'Q, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]

theorem mulVec_single_ne_zero (hPP : P * P' = 1) : P *ᵥ Pi.single ℓ 1 ≠ 0 := by
  intro h
  have hP'P : P' * P = 1 := mul_eq_one_comm.1 hPP
  have h1 : (Pi.single ℓ 1 : Fin n → K) = 0 := by
    calc (Pi.single ℓ 1 : Fin n → K) = (P' * P) *ᵥ Pi.single ℓ 1 := by
          rw [hP'P, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  have h2 := congrFun h1 ℓ
  simp at h2

end Kernel

theorem norton_criterion (M : ι → Matrix (Fin n) (Fin n) K) (theta : List (List ι)) (ℓ : Fin n)
    {P P' Q Q' : Matrix (Fin n) (Fin n) K} (hPP : P * P' = 1) (hQQ : Q * Q' = 1)
    (hD : Q * polyMat M theta * P = diagOne ℓ)
    {uV : ℕ → Fin n → K} {parV : ℕ → ℕ} {labV : ℕ → ι} {Vi : Matrix (Fin n) (Fin n) K}
    (hV : IsSpin M (P *ᵥ Pi.single ℓ 1) uV parV labV) (hVi : Vi * colsMat uV = 1)
    {uW : ℕ → Fin n → K} {parW : ℕ → ℕ} {labW : ℕ → ι} {Wi : Matrix (Fin n) (Fin n) K}
    (hW : IsSpin (fun i => (M i)ᵀ) (Q ℓ) uW parW labW) (hWi : Wi * colsMat uW = 1)
    (U : Submodule K (Fin n → K)) (hU : IsInv M U) : U = ⊥ ∨ U = ⊤ := by
  by_cases htop : U = ⊤
  · exact Or.inr htop
  left
  set Θ := polyMat M theta with hΘ
  have hvU : P *ᵥ Pi.single ℓ 1 ∉ U := fun hv => htop (eq_top_of_spin hV hVi hU hv)
  have hinj : Set.InjOn (Matrix.mulVecLin Θ) U := by
    intro x hx y hy hxy
    have hsub : Θ *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      exact hxy
    have hker := eq_smul_of_mulVec_eq_zero hPP hD hsub
    set c := (P' *ᵥ (x - y)) ℓ with hc
    have hc0 : c = 0 := by
      by_contra hne
      apply hvU
      have hmem : x - y ∈ U := U.sub_mem hx hy
      have : P *ᵥ Pi.single ℓ 1 = c⁻¹ • (x - y) := by
        rw [hker, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact U.smul_mem _ hmem
    rw [hc0, zero_smul] at hker
    exact sub_eq_zero.1 hker
  have hsurj : Set.SurjOn (Matrix.mulVecLin Θ) U U := by
    have : FiniteDimensional K U := inferInstance
    exact (LinearMap.injOn_iff_surjOn (fun x hx => polyMat_mulVec_mem hU theta hx)).1 hinj
  have hdet : Θ.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, mulVec_single_ne_zero hPP,
      mulVec_eq_zero_of_diag hQQ hD⟩
  obtain ⟨b, hb0, hbΘ⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hbw := eq_smul_of_vecMul_eq_zero hQQ hD hbΘ
  set c := (b ᵥ* Q') ℓ with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hb0
    rw [hbw, h0, zero_smul]
  have hbU : b ∈ dotPerp U := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hsurj hx
    rw [Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, hbΘ, zero_dotProduct]
  have hwU : Q ℓ ∈ dotPerp U := by
    have : Q ℓ = c⁻¹ • b := by
      rw [hbw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact (dotPerp U).smul_mem _ hbU
  have hall : dotPerp U = ⊤ := eq_top_of_spin hW hWi (isInv_transpose_dotPerp hU) hwU
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  funext j
  have h1 : (Pi.single j 1 : Fin n → K) ∈ dotPerp U := by
    rw [hall]
    trivial
  have h2 := h1 x hx
  simpa using h2

end CFSG.Sporadic.Co1.Module.CoTwo
