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

namespace CFSG.RankThree.PartOne.HNB

theorem nonempty_mulEquiv_closure_of_kernels {A B : Type*} [Group A] [Group B] (a1 a2 : A)
    (b1 b2 : B)
    (h1 : ∀ w ∈ Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B)), w.1 = 1 → w.2 = 1)
    (h2 : ∀ w ∈ Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B)), w.2 = 1 → w.1 = 1) :
    Nonempty (Subgroup.closure ({a1, a2} : Set A) ≃* Subgroup.closure ({b1, b2} : Set B)) := by
  set Γ := Subgroup.closure ({(a1, b1), (a2, b2)} : Set (A × B)) with hΓ
  let φ : Γ →* A := (MonoidHom.fst A B).comp Γ.subtype
  let ψ : Γ →* B := (MonoidHom.snd A B).comp Γ.subtype
  have hφ : φ.range = Subgroup.closure ({a1, a2} : Set A) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hΓ, MonoidHom.map_closure, Set.image_pair]
    rfl
  have hψ : ψ.range = Subgroup.closure ({b1, b2} : Set B) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hΓ, MonoidHom.map_closure, Set.image_pair]
    rfl
  have hker : φ.ker = ψ.ker := by
    ext w
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun h => h1 w w.2 h, fun h => h2 w w.2 h⟩
  let e : φ.range ≃* ψ.range := (QuotientGroup.quotientKerEquivRange φ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange ψ))
  exact ⟨(MulEquiv.subgroupCongr hφ.symm).trans (e.trans (MulEquiv.subgroupCongr hψ))⟩

theorem mem_submonoidClosure_of_mem_closure {G : Type*} [Group G] [Finite G] {S : Set G} {x : G}
    (hx : x ∈ Subgroup.closure S) : x ∈ Submonoid.closure S := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact Submonoid.subset_closure hx
  | one => exact Submonoid.one_mem _
  | mul x y _ _ hx hy => exact Submonoid.mul_mem _ hx hy
  | inv x _ hx =>
    have h : x⁻¹ = x ^ (orderOf x - 1) := by
      have hpos : 0 < orderOf x := orderOf_pos x
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    rw [h]
    exact Submonoid.pow_mem _ hx _

end CFSG.RankThree.PartOne.HNB
