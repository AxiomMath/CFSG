module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
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
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

namespace CFSG.RankThree.EvenCubic

open Polynomial Matrix

variable {K : Type} [Field K] [Fintype K] {K₃ : Type} [Field K₃] [Algebra K K₃]

@[expose] def cubicTrace (σ : K₃ ≃+* K₃) (b : K₃) : K₃ := b + σ b + σ (σ b)

@[expose] def circulantP (σ : K₃ ≃+* K₃) (θ : K₃) : Matrix (Fin 3) (Fin 3) K₃ :=
  !![θ, σ θ, σ (σ θ); σ (σ θ), θ, σ θ; σ θ, σ (σ θ), θ]

@[expose] def hankelP (σ : K₃ ≃+* K₃) (θ : K₃) : Matrix (Fin 3) (Fin 3) K₃ :=
  !![θ, σ θ, σ (σ θ); σ θ, σ (σ θ), θ; σ (σ θ), θ, σ θ]

theorem mem_range_of_pow_card_eq [Finite K₃] {x : K₃} (hx : x ^ Fintype.card K = x) :
    x ∈ Set.range (algebraMap K K₃) := by
  classical
  by_contra hxK
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  set f : K₃[X] := X ^ Fintype.card K - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K₃ hq
  have hroot : ∀ y : K₃, y ^ Fintype.card K = y → y ∈ f.roots.toFinset := fun y hy => by
    rw [Multiset.mem_toFinset, mem_roots', IsRoot, hf, eval_sub, eval_pow, eval_X, hy, sub_self]
    exact ⟨hf0, rfl⟩
  have hsub : insert x (Finset.univ.image (algebraMap K K₃)) ⊆ f.roots.toFinset := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with rfl | ⟨a, -, rfl⟩
    · exact hroot _ hx
    · exact hroot _ (by rw [← map_pow, FiniteField.pow_card])
  have h1 := Finset.card_le_card hsub
  have h2 : (insert x (Finset.univ.image (algebraMap K K₃))).card = Fintype.card K + 1 := by
    rw [Finset.card_insert_of_notMem (by simpa using hxK),
      Finset.card_image_of_injective _ (algebraMap K K₃).injective, Finset.card_univ]
  have h3 : f.roots.toFinset.card ≤ Fintype.card K :=
    (Multiset.toFinset_card_le _).trans ((card_roots' f).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq K₃ hq).le)
  omega

theorem perm_three_cases : ∀ π : Equiv.Perm (Fin 3), π ^ 3 = 1 → π ≠ 1 →
    π = finRotate 3 ∨ π = (finRotate 3)⁻¹ := by decide

theorem pair_relation [CharP K₃ 2] {c x y : K₃} (hx : x ^ 3 + x ^ 2 + c = 0)
    (hy : y ^ 3 + y ^ 2 + c = 0) (hxy : x ≠ y) : x ^ 2 + x * y + y ^ 2 + x + y = 0 := by
  have h2 : (2 : K₃) = 0 := CharTwo.two_eq_zero
  have hsum : x + y ≠ 0 := fun h => hxy (by
    have := CharTwo.add_eq_zero.mp h
    exact this)
  have key : (x + y) * (x ^ 2 + x * y + y ^ 2 + x + y) = 0 := by
    linear_combination hx + hy + (x ^ 2 * y + x * y ^ 2 + x * y - c) * h2
  exact (mul_eq_zero.mp key).resolve_left hsum

theorem even_cubic_self_dual_basis_and_orthogonal_three_cycle_coboundary [CharP K 2]
    [FiniteDimensional K K₃] (h3 : Module.finrank K K₃ = 3) (σ : K₃ ≃+* K₃)
    (hσ : ∀ b, σ b = b ^ Fintype.card K) (c : K) (hc : ∀ t : K, t ^ 3 + t ^ 2 ≠ c) (θ : K₃)
    (hθ : θ ^ 3 + θ ^ 2 + algebraMap K K₃ c = 0) :
    c ≠ 0 ∧ Irreducible (X ^ 3 + X ^ 2 + C c : K[X]) ∧
    (∃ B : Module.Basis (Fin 3) K K₃, ⇑B = ![θ, σ θ, σ (σ θ)]) ∧
    (∀ i j : Fin 3, cubicTrace σ ((σ ^ (i : ℕ)) θ * (σ ^ (j : ℕ)) θ) = if i = j then 1 else 0) ∧
    ∀ π : Equiv.Perm (Fin 3), π.IsThreeCycle →
      ∃ P : Matrix.SpecialLinearGroup (Fin 3) K₃,
        (P : Matrix (Fin 3) (Fin 3) K₃) = (if π = finRotate 3 then circulantP σ θ
          else hankelP σ θ) ∧
        (P : Matrix (Fin 3) (Fin 3) K₃) * (P : Matrix (Fin 3) (Fin 3) K₃)ᵀ = 1 ∧
        (π.permMatrix K).map (algebraMap K K₃) * (P : Matrix (Fin 3) (Fin 3) K₃).map σ = P ∧
        (π.permMatrix K).map (algebraMap K K₃) =
          (P : Matrix (Fin 3) (Fin 3) K₃) * ((P : Matrix (Fin 3) (Fin 3) K₃).map σ)⁻¹ ∧
        (π.permMatrix K).map (algebraMap K K₃) =
          (P : Matrix (Fin 3) (Fin 3) K₃) * ((P : Matrix (Fin 3) (Fin 3) K₃).map σ)ᵀ := by
  classical
  have : CharP K₃ 2 := charP_of_injective_algebraMap (algebraMap K K₃).injective 2
  have : Finite K₃ := Module.finite_of_finite K
  have := Fintype.ofFinite K₃
  have h2 : (2 : K₃) = 0 := CharTwo.two_eq_zero
  have hc0 : c ≠ 0 := fun h => hc 0 (by rw [h]; ring)
  have hnoroot : ∀ t : K, t ^ 3 + t ^ 2 + c ≠ 0 := fun t ht => hc t (by
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination ht - c * h2K)
  have hirr : Irreducible (X ^ 3 + X ^ 2 + C c : K[X]) := by
    have hdeg : (X ^ 3 + X ^ 2 + C c : K[X]).natDegree = 3 := by compute_degree!
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun t ht => ?_
    apply hnoroot t
    simpa [IsRoot] using ht
  have hcard : Fintype.card K₃ = Fintype.card K ^ 3 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := K₃), h3]
  have hσ3 : ∀ b, σ (σ (σ b)) = b := fun b => by
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    have hq3 : Fintype.card K * (Fintype.card K * Fintype.card K) = Fintype.card K₃ := by
      rw [hcard]; ring
    rw [hq3, FiniteField.pow_card]
  have hσK : ∀ t : K, σ (algebraMap K K₃ t) = algebraMap K K₃ t := fun t => by
    rw [hσ, ← map_pow, FiniteField.pow_card]
  set a := θ with ha
  set b := σ θ with hb
  set d := σ (σ θ) with hd
  set c' := algebraMap K K₃ c with hc'
  have hroot : ∀ x : K₃, x ^ 3 + x ^ 2 + c' = 0 → σ x ^ 3 + σ x ^ 2 + c' = 0 := fun x hx => by
    have := congrArg σ hx
    rwa [map_add, map_add, map_pow, map_pow, hσK, map_zero] at this
  have hra : a ^ 3 + a ^ 2 + c' = 0 := hθ
  have hrb : b ^ 3 + b ^ 2 + c' = 0 := hroot a hra
  have hrd : d ^ 3 + d ^ 2 + c' = 0 := hroot b hrb
  have hab : a ≠ b := by
    intro h
    have hfix : θ ^ Fintype.card K = θ := by rw [← hσ]; exact h.symm
    obtain ⟨t, ht⟩ := mem_range_of_pow_card_eq hfix
    apply hnoroot t
    apply (algebraMap K K₃).injective
    rw [map_add, map_add, map_pow, map_pow, ht, map_zero]
    exact hθ
  have hσa : σ a = b := rfl
  have hσb : σ b = d := rfl
  have hσd : σ d = a := hσ3 θ
  have hbd : b ≠ d := fun h => hab (σ.injective h)
  have had : a ≠ d := fun h => hab (by
    have h' := congrArg σ h
    rw [hσd] at h'
    exact h'.symm)
  have Eab := pair_relation hra hrb hab
  have Ebd := pair_relation hrb hrd hbd
  have Ead := pair_relation hra hrd had
  have he2 : a * b + b * d + d * a = 0 := by
    linear_combination Eab + Ebd + Ead - (a ^ 2 + b ^ 2 + d ^ 2 + a + b + d) * h2
  have he1 : a + b + d = 1 := by
    have hbd0 : b + d ≠ 0 := fun h => hbd (CharTwo.add_eq_zero.mp h)
    have key : (b + d) * (a + b + d + 1) = 0 := by
      linear_combination Eab + Ead + (b * d - a ^ 2 - a) * h2
    have := (mul_eq_zero.mp key).resolve_left hbd0
    linear_combination this - h2
  have hsq : a ^ 2 + b ^ 2 + d ^ 2 = 1 := by
    have : (a + b + d) ^ 2 = 1 := by rw [he1, one_pow]
    linear_combination this - (a * b + b * d + d * a) * h2
  have hT : ∀ x y : K₃, cubicTrace σ (x * y) = x * y + σ x * σ y + σ (σ x) * σ (σ y) :=
    fun x y => by simp only [cubicTrace, map_mul]
  have Taa : cubicTrace σ (a * a) = 1 := by
    rw [hT]; simp only [hσa, hσb]; linear_combination hsq
  have Tbb : cubicTrace σ (b * b) = 1 := by
    rw [hT]; simp only [hσb, hσd]; linear_combination hsq
  have Tdd : cubicTrace σ (d * d) = 1 := by
    rw [hT]; simp only [hσa, hσd]; linear_combination hsq
  have Tab : cubicTrace σ (a * b) = 0 := by
    rw [hT]; simp only [hσa, hσb, hσd]; linear_combination he2
  have Tba : cubicTrace σ (b * a) = 0 := by
    rw [hT]; simp only [hσa, hσb, hσd]; linear_combination he2
  have Tad : cubicTrace σ (a * d) = 0 := by
    rw [hT]; simp only [hσa, hσb, hσd]; linear_combination he2
  have Tda : cubicTrace σ (d * a) = 0 := by
    rw [hT]; simp only [hσa, hσb, hσd]; linear_combination he2
  have Tbd : cubicTrace σ (b * d) = 0 := by
    rw [hT]; simp only [hσa, hσb, hσd]; linear_combination he2
  have Tdb : cubicTrace σ (d * b) = 0 := by
    rw [hT]; simp only [hσa, hσb, hσd]; linear_combination he2
  have hp2 : ∀ x : K₃, (σ ^ 2) x = σ (σ x) := fun x => by rw [pow_two]; rfl
  have htr : ∀ i j : Fin 3,
      cubicTrace σ ((σ ^ (i : ℕ)) a * (σ ^ (j : ℕ)) a) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hp2, hσa, hσb, Taa, Tbb, Tdd, Tab, Tba, Tad, Tda, Tbd, Tdb]
  have hTlin : ∀ (t₁ t₂ t₃ : K) (x y z : K₃),
      cubicTrace σ (algebraMap K K₃ t₁ * x + algebraMap K K₃ t₂ * y + algebraMap K K₃ t₃ * z) =
        algebraMap K K₃ t₁ * cubicTrace σ x + algebraMap K K₃ t₂ * cubicTrace σ y +
          algebraMap K K₃ t₃ * cubicTrace σ z := by
    intro t₁ t₂ t₃ x y z
    simp only [cubicTrace, map_add, map_mul, hσK]
    ring
  have hli : LinearIndependent K ![a, b, d] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Algebra.smul_def] at hg
    have key : ∀ v : K₃, cubicTrace σ (algebraMap K K₃ (g 0) * (v * a) +
        algebraMap K K₃ (g 1) * (v * b) + algebraMap K K₃ (g 2) * (v * d)) = 0 := fun v => by
      have : algebraMap K K₃ (g 0) * (v * a) + algebraMap K K₃ (g 1) * (v * b) +
          algebraMap K K₃ (g 2) * (v * d) = v * (algebraMap K K₃ (g 0) * a +
            algebraMap K K₃ (g 1) * b + algebraMap K K₃ (g 2) * d) := by ring
      rw [this, hg, mul_zero]
      simp [cubicTrace]
    have k0 := key a
    have k1 := key b
    have k2 := key d
    rw [hTlin, Taa, Tab, Tad] at k0
    rw [hTlin, Tba, Tbb, Tbd] at k1
    rw [hTlin, Tda, Tdb, Tdd] at k2
    simp only [mul_one, mul_zero, add_zero, zero_add, map_eq_zero_iff _
      (algebraMap K K₃).injective] at k0 k1 k2
    intro i
    fin_cases i
    · exact k0
    · exact k1
    · exact k2
  have hbasis : ∃ B : Module.Basis (Fin 3) K K₃, ⇑B = ![a, b, d] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, h3]),
      by rw [coe_basisOfLinearIndependentOfCardEqFinrank]⟩
  refine ⟨hc0, hirr, hbasis, htr, ?_⟩
  intro π hπ
  have hπ3 : π = finRotate 3 ∨ π = (finRotate 3)⁻¹ := by
    have h1 := pow_orderOf_eq_one π
    rw [hπ.orderOf] at h1
    refine perm_three_cases π h1 fun h => ?_
    have := hπ.orderOf
    rw [h, orderOf_one] at this
    omega
  have hmapT : ∀ X : Matrix (Fin 3) (Fin 3) K₃,
      X * Xᵀ = 1 → X.map σ * (X.map σ)ᵀ = 1 := fun X hX => by
    rw [← Matrix.transpose_map, ← RingEquiv.mapMatrix_apply, ← RingEquiv.mapMatrix_apply,
      ← map_mul, hX, map_one]
  have hdet : ∀ X : Matrix (Fin 3) (Fin 3) K₃, X * Xᵀ = 1 → X.det = 1 := fun X hX => by
    have h1 := congrArg Matrix.det hX
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    have h2' : (X.det + 1) ^ 2 = 0 := by linear_combination h1 + (X.det + 1) * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2'
    linear_combination this - h2
  have hfinish : ∀ (M X : Matrix (Fin 3) (Fin 3) K₃), X * Xᵀ = 1 → M * X.map σ = X →
      M = X * (X.map σ)⁻¹ ∧ M = X * (X.map σ)ᵀ := fun M X hX hMX => by
    have hinv : (X.map σ)⁻¹ = (X.map σ)ᵀ := Matrix.inv_eq_right_inv (hmapT X hX)
    have hM : M = X * (X.map σ)ᵀ := by
      calc M = M * (X.map σ * (X.map σ)ᵀ) := by rw [hmapT X hX, Matrix.mul_one]
        _ = X * (X.map σ)ᵀ := by rw [← Matrix.mul_assoc, hMX]
    exact ⟨by rw [hinv]; exact hM, hM⟩
  rcases hπ3 with rfl | rfl
  ·
    have hPP : circulantP σ a * (circulantP σ a)ᵀ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [circulantP, Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | linear_combination hsq | linear_combination he2
    have hM : ((finRotate 3).permMatrix K).map (algebraMap K K₃) * (circulantP σ a).map σ =
        circulantP σ a := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [circulantP, Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hσ3]
    obtain ⟨h1, h2'⟩ := hfinish _ _ hPP hM
    exact ⟨⟨circulantP σ a, hdet _ hPP⟩, by simp, hPP, hM, h1, h2'⟩
  ·
    have hne : (finRotate 3)⁻¹ ≠ finRotate 3 := by decide
    have hPP : hankelP σ a * (hankelP σ a)ᵀ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hankelP, Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | linear_combination hsq | linear_combination he2
    have hM : ((finRotate 3)⁻¹.permMatrix K).map (algebraMap K K₃) * (hankelP σ a).map σ =
        hankelP σ a := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hankelP, Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hσ3]
    obtain ⟨h1, h2'⟩ := hfinish _ _ hPP hM
    exact ⟨⟨hankelP σ a, hdet _ hPP⟩, by simp [hne], hPP, hM, h1, h2'⟩

end CFSG.RankThree.EvenCubic
