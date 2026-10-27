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
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

variable {G : Type*} [Group G]

private lemma conj_mem_of_mem_closure {S : Set G} {K : Subgroup G} {c : G}
    (hS : ∀ s ∈ S, c * s * c⁻¹ ∈ K) {x : G} (hx : x ∈ Subgroup.closure S) :
    c * x * c⁻¹ ∈ K := by
  have h : Subgroup.closure S ≤ K.comap (MulEquiv.toMonoidHom (MulAut.conj c)) := by
    rw [Subgroup.closure_le]
    intro s hs
    simpa [Subgroup.mem_comap, MulAut.conj_apply] using hS s hs
  simpa [Subgroup.mem_comap, MulAut.conj_apply] using h hx

theorem mem_normalizer_of_normalClosure {Y N : Subgroup G} (hNY : N ≤ Y)
    (hN : (N.subgroupOf Y).Normal) [IsSimpleGroup N] {b : G} (hbN : b ∈ N) (hb1 : b ≠ 1)
    {g : G} (hgY : g ∈ Subgroup.normalizer (Y : Set G)) (hgb : g * b = b * g) :
    g ∈ Subgroup.normalizer (N : Set G) := by
  have hbY : b ∈ Y := hNY hbN
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G,
      M = Subgroup.closure {x : G | ∃ y ∈ Y, x = y * b * y⁻¹} := ⟨_, rfl⟩
  have hgen : ∀ y ∈ Y, y * b * y⁻¹ ∈ M := by
    intro y hy
    rw [hM]
    exact Subgroup.subset_closure ⟨y, hy, rfl⟩
  have hMN : M ≤ N := by
    rw [hM, Subgroup.closure_le]
    rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp
      (hN.conj_mem ⟨b, hbY⟩ (Subgroup.mem_subgroupOf.mpr hbN) ⟨y, hy⟩)
  have hconjY : ∀ n ∈ Y, ∀ x ∈ M, n * x * n⁻¹ ∈ M := by
    intro n hn x hx
    rw [hM] at hx ⊢
    refine conj_mem_of_mem_closure ?_ hx
    rintro s ⟨y, hy, rfl⟩
    rw [show n * (y * b * y⁻¹) * n⁻¹ = (n * y) * b * (n * y)⁻¹ by group]
    exact Subgroup.subset_closure ⟨n * y, mul_mem hn hy, rfl⟩
  have hMN_normal : (M.subgroupOf N).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hconjY (g : G) (hNY g.2) (n : G) hn
  have hNM : N ≤ M := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf N) with hbot | htop
    · exfalso
      have hbM : b ∈ M := by simpa using hgen 1 Y.one_mem
      have h1 : (⟨b, hbN⟩ : N) ∈ M.subgroupOf N := Subgroup.mem_subgroupOf.mpr hbM
      rw [hbot, Subgroup.mem_bot] at h1
      exact hb1 (congrArg Subtype.val h1)
    · intro x hx
      have h2 : (⟨x, hx⟩ : N) ∈ M.subgroupOf N := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h2
  have hconjG : ∀ c : G, c ∈ Subgroup.normalizer (Y : Set G) → c * b = b * c →
      ∀ x ∈ M, c * x * c⁻¹ ∈ M := by
    intro c hc hcb x hx
    rw [hM] at hx ⊢
    refine conj_mem_of_mem_closure ?_ hx
    rintro s ⟨y, hy, rfl⟩
    have hb' : c⁻¹ * b * c = b := by
      rw [mul_assoc, ← hcb, inv_mul_cancel_left]
    have hcy : c * y * c⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hc y).mp hy
    have e : (c * y * c⁻¹) * b * (c * y * c⁻¹)⁻¹ = c * (y * b * y⁻¹) * c⁻¹ := by
      have e' : (c * y * c⁻¹) * b * (c * y * c⁻¹)⁻¹ = c * y * (c⁻¹ * b * c) * y⁻¹ * c⁻¹ := by
        group
      rw [e', hb']
      group
    rw [← e]
    exact Subgroup.subset_closure ⟨c * y * c⁻¹, hcy, rfl⟩
  have hginv : g⁻¹ ∈ Subgroup.normalizer (Y : Set G) := inv_mem hgY
  have hginvb : g⁻¹ * b = b * g⁻¹ := Commute.inv_left (show Commute g b from hgb)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hMN (hconjG g hgY hgb x (hNM hx))
  · intro hx
    have h3 := hconjG g⁻¹ hginv hginvb (g * x * g⁻¹) (hNM hx)
    have e2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e2] at h3
    exact hMN h3

end CFSG.RankThree.PartTwo.Sec21.Hering233i
