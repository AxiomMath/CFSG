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

public section

namespace CFSG.RankThree.PartOne.K133

open Polynomial

theorem eigen_independence {K : Type} [Field K] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {E : Type} [Group E] [Finite E] (μ : E → Fin 4 → K)
    (hmul : ∀ g h j, μ (g * h) j = μ g j * μ h j)
    (hpow : ∀ g j, μ g j ^ p = 1)
    (hprod : ∀ g, μ g 0 * μ g 1 * μ g 2 * μ g 3 = 1)
    (hinj : ∀ g, (∀ j, μ g j = 1) → g = 1)
    (hcard : p ^ 3 ≤ Nat.card E) :
    (∀ j k, j ≠ k → ∃ g, μ g j ≠ μ g k) ∧ (∀ j k, ∃ g, μ g j * μ g k ≠ 1) := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hp0 : 0 < p := hp.pos
  have hne0 : ∀ g j, μ g j ≠ 0 := fun g j h0 => by
    have := hpow g j
    rw [h0, zero_pow hp.ne_zero] at this
    exact zero_ne_one this
  have hone : ∀ j, μ 1 j = 1 := fun j => by
    have h := hmul 1 1 j
    rw [mul_one] at h
    exact (mul_eq_left₀ (hne0 1 j)).1 h.symm
  have hinv : ∀ g j, μ g⁻¹ j = (μ g j)⁻¹ := fun g j => by
    have h := hmul g g⁻¹ j
    rw [mul_inv_cancel, hone] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  let Φ : E → (Fin 3 → K) := fun g i => μ g i.castSucc
  have hΦinj : Function.Injective Φ := by
    intro g h hgh
    have h1 : ∀ i : Fin 3, μ (g * h⁻¹) i.castSucc = 1 := fun i => by
      rw [hmul, hinv]
      have : μ g i.castSucc = μ h i.castSucc := congrFun hgh i
      rw [this]
      exact mul_inv_cancel₀ (hne0 h _)
    have h3 : μ (g * h⁻¹) 3 = 1 := by
      have := hprod (g * h⁻¹)
      have e0 := h1 0
      have e1 := h1 1
      have e2 := h1 2
      simp only [Fin.castSucc_zero] at e0
      change μ (g * h⁻¹) 0 = 1 at e0
      change μ (g * h⁻¹) 1 = 1 at e1
      change μ (g * h⁻¹) 2 = 1 at e2
      rw [e0, e1, e2] at this
      simpa using this
    have := hinj (g * h⁻¹) fun j => by
      fin_cases j
      · exact h1 0
      · exact h1 1
      · exact h1 2
      · exact h3
    exact mul_inv_eq_one.1 this
  let R : Finset K := nthRootsFinset p (1 : K)
  have hRcard : R.card = p := hζ.card_nthRootsFinset
  have hmemR : ∀ x : K, x ∈ R ↔ x ^ p = 1 := fun x => mem_nthRootsFinset hp0 (1 : K)
  let S : Finset (Fin 3 → K) := Fintype.piFinset (fun _ : Fin 3 => R)
  have hScard : S.card = p ^ 3 := by
    simp [S, Fintype.card_piFinset, hRcard]
  have hsub : Finset.univ.image Φ ⊆ S := by
    intro f hf
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hf
    exact Fintype.mem_piFinset.2 fun i => (hmemR _).2 (hpow g _)
  have himgcard : (Finset.univ.image Φ).card = Nat.card E := by
    rw [Finset.card_image_of_injective _ hΦinj, Finset.card_univ, Nat.card_eq_fintype_card]
  have heq : Finset.univ.image Φ = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hScard, himgcard]; exact hcard)
  have hsurj : ∀ f : Fin 3 → K, (∀ i, f i ^ p = 1) → ∃ g, ∀ i : Fin 3, μ g i.castSucc = f i := by
    intro f hf
    have : f ∈ S := Fintype.mem_piFinset.2 fun i => (hmemR _).2 (hf i)
    rw [← heq] at this
    obtain ⟨g, -, hg⟩ := Finset.mem_image.1 this
    exact ⟨g, fun i => congrFun hg i⟩
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := by
    intro h
    have := hζ.eq_orderOf
    rw [h, orderOf_one] at this
    omega
  have hζk : ∀ k : ℕ, 0 < k → k < p → ζ ^ k ≠ 1 := fun k hk hkp h => by
    have := hζ.pow_eq_one_iff_dvd k
    have := (hζ.pow_eq_one_iff_dvd k).1 h
    have := Nat.le_of_dvd hk this
    omega
  have hζ2 : ζ ^ 2 ≠ 1 := hζk 2 (by norm_num) (by omega)
  have htest : ∀ i : Fin 3, ∃ g, (∀ l : Fin 3, μ g l.castSucc = if l = i then ζ else 1) ∧ μ g 3 = ζ⁻¹ := by
    intro i
    obtain ⟨g, hg⟩ := hsurj (fun l => if l = i then ζ else 1) (fun l => by
      by_cases h : l = i
      · simp [h, hζp]
      · simp [h])
    refine ⟨g, hg, ?_⟩
    have := hprod g
    have e0 : μ g 0 = if (0 : Fin 3) = i then ζ else 1 := hg 0
    have e1 : μ g 1 = if (1 : Fin 3) = i then ζ else 1 := hg 1
    have e2 : μ g 2 = if (2 : Fin 3) = i then ζ else 1 := hg 2
    rw [e0, e1, e2] at this
    fin_cases i <;>
    · have h' : ζ * μ g 3 = 1 := by simpa using this
      exact eq_inv_of_mul_eq_one_right h'
  obtain ⟨g0, h0, h03⟩ := htest 0
  obtain ⟨g1, h1, h13⟩ := htest 1
  obtain ⟨g2, h2, h23⟩ := htest 2
  have hv0 : ∀ l : Fin 4, μ g0 l = if l = 0 then ζ else if l = 3 then ζ⁻¹ else 1 := by
    intro l
    fin_cases l
    · simpa using h0 0
    · simpa using h0 1
    · simpa using h0 2
    · simpa using h03
  have hv1 : ∀ l : Fin 4, μ g1 l = if l = 1 then ζ else if l = 3 then ζ⁻¹ else 1 := by
    intro l
    fin_cases l
    · simpa using h1 0
    · simpa using h1 1
    · simpa using h1 2
    · simpa using h13
  have hv2 : ∀ l : Fin 4, μ g2 l = if l = 2 then ζ else if l = 3 then ζ⁻¹ else 1 := by
    intro l
    fin_cases l
    · simpa using h2 0
    · simpa using h2 1
    · simpa using h2 2
    · simpa using h23
  have hζinv1 : ζ⁻¹ ≠ 1 := by simpa using hζ1
  have hζinvζ : ζ⁻¹ ≠ ζ := by
    intro h
    apply hζ2
    have : ζ * ζ = 1 := by
      have h1 := mul_inv_cancel₀ (hζ.ne_zero hp0.ne')
      rwa [h] at h1
    rw [sq]; exact this
  have hζζ1 : ζ * ζ ≠ 1 := by rw [← sq]; exact hζ2
  have hζinv2 : ζ⁻¹ * ζ⁻¹ ≠ 1 := by
    intro h
    apply hζ2
    have h' := congrArg (fun x => x⁻¹) h
    simp only [mul_inv_rev, inv_inv, inv_one] at h'
    rw [sq]; exact h'
  have hz0 : ζ ≠ 0 := hζ.ne_zero hp0.ne'
  refine ⟨fun j k hjk => ?_, fun j k => ?_⟩
  · fin_cases j <;> fin_cases k <;> simp at hjk
    · exact ⟨g0, by simp only [hv0]; simp [hζ1]⟩
    · exact ⟨g0, by simp only [hv0]; simp [hζ1]⟩
    · exact ⟨g0, by simp only [hv0]; simp [hζinvζ.symm]⟩
    · exact ⟨g1, by simp only [hv1]; simp [hζ1]⟩
    · exact ⟨g1, by simp only [hv1]; simp [hζ1]⟩
    · exact ⟨g1, by simp only [hv1]; simp [hζinvζ.symm]⟩
    · exact ⟨g2, by simp only [hv2]; simp [hζ1]⟩
    · exact ⟨g2, by simp only [hv2]; simp [hζ1]⟩
    · exact ⟨g2, by simp only [hv2]; simp [hζinvζ.symm]⟩
    · exact ⟨g0, by simp only [hv0]; simp [hζinvζ]⟩
    · exact ⟨g1, by simp only [hv1]; simp [hζinvζ]⟩
    · exact ⟨g2, by simp only [hv2]; simp [hζinvζ]⟩
  · fin_cases j <;> fin_cases k
    · exact ⟨g0, by simp only [hv0]; simpa using hζζ1⟩
    · exact ⟨g1, by simp only [hv1]; simpa using hζ1⟩
    · exact ⟨g2, by simp only [hv2]; simpa using hζ1⟩
    · exact ⟨g1, by simp only [hv1]; simpa using hζinv1⟩
    · exact ⟨g0, by simp only [hv0]; simpa using hζ1⟩
    · exact ⟨g1, by simp only [hv1]; simpa using hζζ1⟩
    · exact ⟨g2, by simp only [hv2]; simpa using hζ1⟩
    · exact ⟨g0, by simp only [hv0]; simpa using hζinv1⟩
    · exact ⟨g0, by simp only [hv0]; simpa using hζ1⟩
    · exact ⟨g1, by simp only [hv1]; simpa using hζ1⟩
    · exact ⟨g2, by simp only [hv2]; simpa using hζζ1⟩
    · exact ⟨g0, by simp only [hv0]; simpa using hζinv1⟩
    · exact ⟨g1, by simp only [hv1]; simpa using hζinv1⟩
    · exact ⟨g0, by simp only [hv0]; simpa using hζinv1⟩
    · exact ⟨g1, by simp only [hv1]; simpa using hζinv1⟩
    · exact ⟨g0, by simp only [hv0]; simpa using hζinv2⟩

end CFSG.RankThree.PartOne.K133
