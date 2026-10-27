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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.RankThree.PartOne

theorem conj_injective_of_center_eq_bot {T : Type*} [Group T] (hZ : Subgroup.center T = ⊥) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center T := Subgroup.mem_center_iff.2 fun t => by
    have ht := congrArg (fun φ : MulAut T => φ t) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at ht
    calc t * g = g * t * g⁻¹ * g := by rw [ht]
      _ = g * t := by group
  rwa [hZ, Subgroup.mem_bot] at hc

theorem mulAut_conj_apply_eq_conj_apply {T : Type*} [Group T] (s : MulAut T) (x : T) :
    s * MulAut.conj x * s⁻¹ = MulAut.conj (s x) := by
  ext y
  simp [MulAut.conj_apply]

theorem mulAut_eq_one_of_commute_conj_of_closure_eq_top {T : Type*} [Group T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {S : Set T}
    (hS : Subgroup.closure S = ⊤) {s : MulAut T}
    (h : ∀ x ∈ S, s * MulAut.conj x = MulAut.conj x * s) : s = 1 := by
  have hle : Subgroup.closure S ≤ (Subgroup.centralizer ({s} : Set (MulAut T))).comap
      (MulAut.conj : T →* MulAut T) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (h x hx).symm
  have hall : ∀ x : T, s * MulAut.conj x = MulAut.conj x * s := by
    intro x
    have hx : x ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top x
    have := hle hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  ext x
  have h1 : MulAut.conj (s x) = MulAut.conj x := by
    rw [← mulAut_conj_apply_eq_conj_apply, hall x, mul_assoc, mul_inv_cancel, mul_one]
  simpa using hinj h1

theorem mulAut_eq_one_of_commute_conj_of_surjective {G T : Type*} [Group G] [Group T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) (φ : G →* T)
    (hφ : Function.Surjective φ) {S : Set G} (hS : Subgroup.closure S = ⊤) {s : MulAut T}
    (h : ∀ g ∈ S, s * MulAut.conj (φ g) = MulAut.conj (φ g) * s) : s = 1 := by
  refine mulAut_eq_one_of_commute_conj_of_closure_eq_top hinj (S := φ '' S) ?_ ?_
  · rw [← MonoidHom.map_closure, hS, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact hφ
  · rintro _ ⟨g, hg, rfl⟩
    exact h g hg

theorem mulAut_eq_one_of_commute_conj_of_iSup_eq_top {G T ι : Type*} [Group G] [Group T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) (φ : G →* T)
    (hφ : Function.Surjective φ) (F : ι → Subgroup G) (hF : ⨆ i, F i = ⊤) {s : MulAut T}
    (h : ∀ i, ∀ g ∈ F i, s * MulAut.conj (φ g) = MulAut.conj (φ g) * s) : s = 1 := by
  refine mulAut_eq_one_of_commute_conj_of_surjective hinj φ hφ
    (S := ⋃ i, (F i : Set G)) ?_ ?_
  · rw [← Subgroup.iSup_eq_closure, hF]
  · intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact h i g hi

theorem eq_bot_of_commute_conj_of_iSup_eq_top {G T ι : Type*} [Group G] [Group T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) (φ : G →* T)
    (hφ : Function.Surjective φ) (F : ι → Subgroup G) (hF : ⨆ i, F i = ⊤)
    (I : Subgroup (MulAut T))
    (h : ∀ s ∈ I, ∀ i, ∀ g ∈ F i, s * MulAut.conj (φ g) = MulAut.conj (φ g) * s) : I = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  exact (Subgroup.mem_bot).mpr
    (mulAut_eq_one_of_commute_conj_of_iSup_eq_top hinj φ hφ F hF fun i g hg => h s hs i g hg)

end CFSG.RankThree.PartOne
