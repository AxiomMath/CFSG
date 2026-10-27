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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Sporadic.Co2Smith

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

theorem relIndex_inf_stabilizer (F : Subgroup G) (b : X) :
    (F ⊓ stabilizer G b).relIndex F = (orbit F b).ncard := by
  rw [← MulAction.index_stabilizer, Subgroup.relIndex]
  congr 1
  ext x
  simp [MulAction.mem_stabilizer_iff]

theorem orbit_subset_of_le {T F : Subgroup G} (h : T ≤ F) (b : X) :
    orbit T b ⊆ orbit F b := by
  rintro _ ⟨g, rfl⟩
  exact ⟨⟨g, h g.2⟩, rfl⟩

theorem le_relIndex_of_orbit [Finite X] {T F : Subgroup G} (hTF : T ≤ F) (b : X) {n : ℕ}
    (pts : Fin n → X) (hinj : Function.Injective pts) (hmem : ∀ i, pts i ∈ orbit T b) :
    n ≤ (F ⊓ stabilizer G b).relIndex F := by
  rw [relIndex_inf_stabilizer]
  have h1 : Set.range pts ⊆ orbit F b := fun _ ⟨i, hi⟩ => hi ▸ orbit_subset_of_le hTF b (hmem i)
  calc n = (Set.range pts).ncard := by rw [Set.ncard_range_of_injective hinj, Nat.card_fin]
    _ ≤ (orbit F b).ncard := Set.ncard_le_ncard h1 (Set.toFinite _)

theorem smul_mem_orbit_closure {S : Set G} {b x : X} (hx : x ∈ orbit (Subgroup.closure S) b)
    {g : G} (hg : g ∈ S) : g • x ∈ orbit (Subgroup.closure S) b := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := hx
  refine ⟨⟨g * k, Subgroup.mul_mem _ (Subgroup.subset_closure hg) hk⟩, ?_⟩
  show (g * k) • b = g • k • b
  exact mul_smul g k b

end CFSG.Sporadic.Co2Smith
