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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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

open scoped MatrixGroups Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Flag

theorem eq_one_of_pow_three {F : Type} [Field F] [CharP F 2] (hω : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    {x : F} (hx : x ^ 3 = 1) : x = 1 := by
  have key : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (hω x)

theorem hω_of_card {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hn : Odd n)
    (hF : Fintype.card F = 2 ^ n) : ∀ x : F, x ^ 2 + x + 1 ≠ 0 := by
  intro x hx
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hx3 : x ^ 3 = 1 := by linear_combination (x - 1) * hx
  have hx1 : x ≠ 1 := by
    intro h
    subst h
    have h10 : (1 : F) = 0 := by linear_combination hx - h2
    exact one_ne_zero h10
  have hx0 : x ≠ 0 := by
    intro h
    subst h
    norm_num at hx
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hdvd : orderOf x ∣ Fintype.card F - 1 :=
    orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one x hx0)
  rw [hord, hF] at hdvd
  obtain ⟨m, rfl⟩ := hn
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2n : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num [mul_comm]
  rw [h2n] at hdvd
  have hpos : 0 < 4 ^ m := by positivity
  omega

theorem quad_eq_zero {F : Type} [Field F] (hω : ∀ x : F, x ^ 2 + x + 1 ≠ 0) {β γ : F}
    (hD : β ^ 2 + β * γ + γ ^ 2 = 0) : β = 0 ∧ γ = 0 := by
  by_cases hγ : γ = 0
  · subst hγ
    have hβ : β ^ 2 = 0 := by linear_combination hD
    exact ⟨(pow_eq_zero_iff two_ne_zero).mp hβ, rfl⟩
  · exfalso
    have hγ' : γ * γ⁻¹ = 1 := mul_inv_cancel₀ hγ
    have ht : (β * γ⁻¹) ^ 2 + β * γ⁻¹ + 1 = 0 := by
      linear_combination (γ⁻¹) ^ 2 * hD - (β * γ⁻¹ + γ * γ⁻¹ + 1) * hγ'
    exact hω _ ht

theorem core_zero {F : Type} [Field F] [CharP F 2] (hω : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    {N : Matrix (Fin 3) (Fin 3) F} {v w y φ : Fin 3 → F} (hv : v ≠ 0) (hφ : φ ≠ 0)
    (hφv : φ ⬝ᵥ v = 0) (hφw : φ ⬝ᵥ w = 0) (hφy : φ ⬝ᵥ y = 0)
    (hNv : N *ᵥ v = 0) (hNw : N *ᵥ w = y) (hNy : N *ᵥ y = y + w) : w = 0 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hvφ : v ⬝ᵥ φ = 0 := by rw [dotProduct_comm]; exact hφv
  have hwφ : w ⬝ᵥ φ = 0 := by rw [dotProduct_comm]; exact hφw
  have hyφ : y ⬝ᵥ φ = 0 := by rw [dotProduct_comm]; exact hφy
  have hAφ : Matrix.of ![v, w, y] *ᵥ φ = 0 := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, hvφ, hwφ, hyφ]
  have hdetA : (Matrix.of ![v, w, y]).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨φ, hφ, hAφ⟩
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdetA
  have hR : c 0 • v + c 1 • w + c 2 • y = 0 := by
    funext i
    have hi := congrFun hc i
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three] at hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination hi
  have hc12 : c 1 ^ 2 + c 1 * c 2 + c 2 ^ 2 ≠ 0 := by
    intro hD
    obtain ⟨h1, h2'⟩ := quad_eq_zero hω hD
    have hc0' : c 0 ≠ 0 := by
      intro h0
      apply hc0
      funext i
      fin_cases i <;> simp [h0, h1, h2']
    apply hv
    funext i
    have hi := congrFun hR i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    have hvi : c 0 * v i = 0 := by linear_combination hi - (w i) * h1 - (y i) * h2'
    exact (mul_eq_zero.mp hvi).resolve_left hc0'
  have hR1 : c 1 • y + c 2 • (y + w) = 0 := by
    have hh := congrArg (fun x => N *ᵥ x) hR
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, hNv, hNw, hNy,
      smul_zero, zero_add] at hh
    exact hh
  have hR2 : c 1 • (y + w) + c 2 • (y + w + y) = 0 := by
    have hh := congrArg (fun x => N *ᵥ x) hR1
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, hNw, hNy] at hh
    exact hh
  have E1 : ∀ i, (c 1 + c 2) * y i + c 2 * w i = 0 := by
    intro i
    have hi := congrFun hR1 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    linear_combination hi
  have E2 : ∀ i, c 1 * y i + (c 1 + c 2) * w i = 0 := by
    intro i
    have hi := congrFun hR2 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    linear_combination hi - (c 2 * y i) * h2
  have hDw : ∀ i, (c 1 ^ 2 + c 1 * c 2 + c 2 ^ 2) * w i = 0 := by
    intro i
    linear_combination c 1 * E1 i + (c 1 + c 2) * E2 i - (c 1 * (c 1 + c 2) * y i + c 1 * c 2 * w i) * h2
  funext i
  exact (mul_eq_zero.mp (hDw i)).resolve_left hc12

theorem no_fixed_flag {F : Type} [Field F] [CharP F 2] (hω : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    {g : Matrix (Fin 3) (Fin 3) F} (hg3 : g * g * g = 1) (hg1 : g ≠ 1)
    {v φ : Fin 3 → F} (hv : v ≠ 0) (hφ : φ ≠ 0) (hφv : φ ⬝ᵥ v = 0)
    (hgv : g *ᵥ v = v) (hgφ : φ ᵥ* g = φ) : False := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hone : (1 : Matrix (Fin 3) (Fin 3) F) + 1 = 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.zero_apply]
      linear_combination h2
    · simp [Matrix.one_apply_ne hij]
  have hX2 : ∀ X : Matrix (Fin 3) (Fin 3) F, X + X = 0 := by
    intro X
    calc X + X = X * (1 + 1) := by rw [mul_add, mul_one]
      _ = 0 := by rw [hone, mul_zero]
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 3) (Fin 3) F, N = g - 1 := ⟨_, rfl⟩
  have hN3 : N * N * N = N * N + N := by
    have e : N * N * N - (N * N + N)
        = (g * g * g - 1) - (g * g + g * g) - (g * g + g * g) + (g + g) + (g + g) := by
      rw [hN]
      noncomm_ring
    have e0 : N * N * N - (N * N + N) = 0 := by
      rw [e, hg3, hX2 (g * g), hX2 g] <;> simp
    exact sub_eq_zero.mp e0
  have hNv : N *ᵥ v = 0 := by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, hgv, sub_self]
  have hφN : φ ᵥ* N = 0 := by
    rw [hN, Matrix.vecMul_sub, Matrix.vecMul_one, hgφ, sub_self]
  have hNne : N ≠ 0 := by
    rw [hN]
    exact sub_ne_zero.mpr hg1
  have hall : ∀ u : Fin 3 → F, N *ᵥ u = 0 := by
    intro u
    have hφw : φ ⬝ᵥ (N *ᵥ u) = 0 := by
      rw [Matrix.dotProduct_mulVec, hφN, zero_dotProduct]
    have hφy : φ ⬝ᵥ (N *ᵥ (N *ᵥ u)) = 0 := by
      rw [Matrix.dotProduct_mulVec, hφN, zero_dotProduct]
    have hNy : N *ᵥ (N *ᵥ (N *ᵥ u)) = N *ᵥ (N *ᵥ u) + N *ᵥ u := by
      calc N *ᵥ (N *ᵥ (N *ᵥ u)) = (N * N * N) *ᵥ u := by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        _ = (N * N + N) *ᵥ u := by rw [hN3]
        _ = (N * N) *ᵥ u + N *ᵥ u := by rw [Matrix.add_mulVec]
        _ = N *ᵥ (N *ᵥ u) + N *ᵥ u := by rw [Matrix.mulVec_mulVec]
    exact core_zero hω hv hφ hφv hφw hφy hNv rfl hNy
  apply hNne
  ext i j
  have hij := congrFun (hall (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hij

end CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Flag
