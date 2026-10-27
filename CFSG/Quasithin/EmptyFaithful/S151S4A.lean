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

namespace CFSG.Quasithin.S151S4

open Matrix

variable {K : Type} [Field K]

abbrev SL2 (K : Type) [Field K] := Matrix.SpecialLinearGroup (Fin 2) K

@[expose] def uU (t : K) : SL2 K := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lU (s : K) : SL2 K := ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two]⟩

@[simp] theorem coe_uU (t : K) : ((uU t : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, t; 0, 1] := rfl

@[simp] theorem coe_lU (s : K) : ((lU s : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; s, 1] := rfl

theorem uU_mul (t t' : K) : uU t * uU t' = uU (t + t') := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_mul, add_comm]

@[expose] def Bsub (K : Type) [Field K] : Subgroup (SL2 K) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 at hg
    change (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 at hh
    change ((g * h : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, hh]
  inv_mem' := by
    intro g hg
    change (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 at hg
    change ((g⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hg]

theorem mem_Bsub {g : SL2 K} : g ∈ Bsub K ↔ (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := Iff.rfl

theorem uU_mem_Bsub (t : K) : uU t ∈ Bsub K := by
  rw [mem_Bsub]
  simp

theorem lU_not_mem_Bsub (s : K) (hs : s ≠ 0) : lU s ∉ Bsub K := by
  rw [mem_Bsub]
  simpa using hs

theorem Bsub_ne_top : Bsub K ≠ ⊤ := by
  intro h
  have : lU (1 : K) ∈ Bsub K := h ▸ Subgroup.mem_top _
  exact lU_not_mem_Bsub (1 : K) one_ne_zero this

theorem eq_uU_lU_uU (g : SL2 K) (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    g = uU (((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) *
        lU ((g : Matrix (Fin 2) (Fin 2) K) 1 0) *
        uU (((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) K) 0 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [coe_uU, coe_lU, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
    first | ring1 | linear_combination hdet | linear_combination (-1 : K) * hdet

theorem mem_of_uU_lU {H : Subgroup (SL2 K)} (hu : ∀ t : K, uU t ∈ H) (hl : ∀ s : K, lU s ∈ H)
    (g : SL2 K) : g ∈ H := by
  have key : ∀ g : SL2 K, (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 → g ∈ H := by
    intro g hc
    rw [eq_uU_lU_uU g hc]
    exact H.mul_mem (H.mul_mem (hu _) (hl _)) (hu _)
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have hdet : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
      have := g.2
      rw [Matrix.det_fin_two, hc] at this
      simpa using this
    have ha : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hdet
      exact zero_ne_one hdet
    have h1 : lU (1 : K) * g ∈ H := by
      apply key
      simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc] using ha
    have : g = (lU (1 : K))⁻¹ * (lU (1 : K) * g) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem (hl 1)) h1
  · exact key g hc

theorem borel_or_top [CharP K 2] {H : Subgroup (SL2 K)} (hu : ∀ t : K, uU t ∈ H) :
    H ≤ Bsub K ∨ H = ⊤ := by
  by_cases hB : ∀ g ∈ H, g ∈ Bsub K
  · exact Or.inl hB
  right
  push Not at hB
  obtain ⟨g, hgH, hgB⟩ := hB
  have hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := fun h => hgB h
  have hdet : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) K) 0 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  set a := (g : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) K) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) K) 1 0 with hc'
  set d := (g : Matrix (Fin 2) (Fin 2) K) 1 1 with hd
  obtain ⟨n, hn⟩ : ∃ n : SL2 K, n = uU (a / c) * g := ⟨_, rfl⟩
  have hnH : n ∈ H := hn ▸ H.mul_mem (hu _) hgH
  have hnmat : (n : Matrix (Fin 2) (Fin 2) K) = !![0, c⁻¹; c, d] := by
    rw [hn, Matrix.SpecialLinearGroup.coe_mul, coe_uU, Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) K)]
    simp only [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← ha, ← hb, ← hc', ← hd] <;> field_simp
    · linear_combination a * h2
    · linear_combination hdet + b * c * h2
  have hl : ∀ s : K, lU s ∈ H := by
    intro s
    have hnu : n * uU (s / c ^ 2) * n⁻¹ ∈ H := H.mul_mem (H.mul_mem hnH (hu _)) (H.inv_mem hnH)
    have heq : lU s = n * uU (s / c ^ 2) * n⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hnmat, coe_uU, coe_lU]
      simp only [Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j
      · simp
      · simp
      · simp
      · simp
        field_simp
    rw [heq]
    exact hnu
  exact eq_top_iff.mpr fun g' _ => mem_of_uU_lU hu hl g'

end CFSG.Quasithin.S151S4
