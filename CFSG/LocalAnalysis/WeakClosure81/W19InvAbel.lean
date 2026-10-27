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
public import Mathlib.GroupTheory.FixedPointFree
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

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped Pointwise commutatorElement

variable {Q : Type*} [Group Q] [Finite Q]

theorem inv_and_comm_of_fixedPointFree {R X : Subgroup Q} {a : Q}
    (hXR : X ≤ normalizer (R : Set Q)) (haR : a ∈ normalizer (R : Set Q))
    (haX : a ∈ normalizer ((X ⊔ R : Subgroup Q) : Set Q)) (ha2 : a * a ∈ R)
    (hfpf : ∀ x ∈ X, ⁅a, x⁆ ∈ R → x ∈ R) :
    (∀ x ∈ X, a * x * a⁻¹ * x ∈ R) ∧ ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ R := by
  classical
  have hRX : R ≤ X ⊔ R := le_sup_right
  have hZn : X ⊔ R ≤ normalizer (R : Set Q) := sup_le hXR Subgroup.le_normalizer
  haveI hnorm : (R.subgroupOf (X ⊔ R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRX).2 hZn
  let c : ↥(X ⊔ R) →* ↥(X ⊔ R) :=
    { toFun := fun z => ⟨a * z * a⁻¹, (Subgroup.mem_normalizer_iff.1 haX z).1 z.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun z w => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hc : R.subgroupOf (X ⊔ R) ≤ (R.subgroupOf (X ⊔ R)).comap c := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.1 haR _).1 hz
  let φ : ↥(X ⊔ R) ⧸ R.subgroupOf (X ⊔ R) →* ↥(X ⊔ R) ⧸ R.subgroupOf (X ⊔ R) :=
    QuotientGroup.map _ _ c hc
  have hφ : ∀ z : ↥(X ⊔ R), φ (QuotientGroup.mk z) = QuotientGroup.mk (c z) := fun z => rfl
  have hinv : Function.Involutive φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H z =>
      rw [hφ, hφ, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hz : (z : Q) ∈ normalizer (R : Set Q) := hZn z.2
      have hz' : (z : Q)⁻¹ ∈ normalizer (R : Set Q) := hZn (Subgroup.inv_mem _ z.2)
      have h1 : (z : Q)⁻¹ * (a * a)⁻¹ * (z : Q)⁻¹⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.1 hz' ((a * a)⁻¹)).1 (R.inv_mem ha2)
      have key : (((c (c z))⁻¹ * z : ↥(X ⊔ R)) : Q) =
          (a * a) * ((z : Q)⁻¹ * (a * a)⁻¹ * (z : Q)⁻¹⁻¹) := by
        change (a * (a * (z : Q) * a⁻¹) * a⁻¹)⁻¹ * (z : Q) = _
        simp only [mul_inv_rev, inv_inv, mul_assoc]
      rw [key]
      exact R.mul_mem ha2 h1
  have hfp : MonoidHom.FixedPointFree φ := by
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H z =>
      rw [hφ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
      have hprod : ((X ⊔ R : Subgroup Q) : Set Q) = (X : Set Q) * (R : Set Q) :=
        Subgroup.coe_mul_of_left_le_normalizer_right X R hXR
      have hzm : (z : Q) ∈ (X : Set Q) * (R : Set Q) := by rw [← hprod]; exact z.2
      obtain ⟨x, hx, r, hr, hxr⟩ := hzm
      have hxN : x ∈ normalizer (R : Set Q) := hXR hx
      have haxN : a * x * a⁻¹ ∈ normalizer (R : Set Q) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ haR hxN) (Subgroup.inv_mem _ haR)
      have hu : a * r * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 haR r).1 hr
      have ht : (a * x * a⁻¹)⁻¹ * x ∈ R := by
        have h1 : ((c z)⁻¹ * z : ↥(X ⊔ R)).1 = (a * r * a⁻¹)⁻¹ * ((a * x * a⁻¹)⁻¹ * x) * r := by
          change (a * (z : Q) * a⁻¹)⁻¹ * (z : Q) = _
          rw [← hxr]
          group
        rw [h1] at hq
        have h2 := R.mul_mem (R.mul_mem hu hq) (R.inv_mem hr)
        have h3 : a * r * a⁻¹ * ((a * r * a⁻¹)⁻¹ * ((a * x * a⁻¹)⁻¹ * x) * r) * r⁻¹ =
            (a * x * a⁻¹)⁻¹ * x := by group
        rwa [h3] at h2
      have hcommax : ⁅a, x⁆ ∈ R := by
        have h1 := (Subgroup.mem_normalizer_iff.1 haxN (((a * x * a⁻¹)⁻¹ * x)⁻¹)).1 (R.inv_mem ht)
        have h2 : a * x * a⁻¹ * ((a * x * a⁻¹)⁻¹ * x)⁻¹ * (a * x * a⁻¹)⁻¹ = ⁅a, x⁆ := by
          rw [commutatorElement_def]; group
        rw [h2] at h1
        exact h1
      have hxR : x ∈ R := hfpf x hx hcommax
      have hzR : (z : Q) ∈ R := by rw [← hxr]; exact R.mul_mem hxR hr
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hzR
  have hinvφ := hfp.coe_eq_inv_of_involutive hinv
  have hcomm := hfp.commute_all_of_involutive hinv
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have h1 := congrFun hinvφ (QuotientGroup.mk (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(X ⊔ R)))
    rw [hφ] at h1
    have h2 : (QuotientGroup.mk ((c ⟨x, Subgroup.mem_sup_left hx⟩) *
        ⟨x, Subgroup.mem_sup_left hx⟩) : ↥(X ⊔ R) ⧸ R.subgroupOf (X ⊔ R)) = 1 := by
      rw [QuotientGroup.mk_mul]
      have h3 : (QuotientGroup.mk (c ⟨x, Subgroup.mem_sup_left hx⟩) :
          ↥(X ⊔ R) ⧸ R.subgroupOf (X ⊔ R)) =
          (QuotientGroup.mk (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(X ⊔ R)))⁻¹ := h1
      rw [h3, inv_mul_cancel]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2
  · have h1 := hcomm (QuotientGroup.mk (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(X ⊔ R)))
      (QuotientGroup.mk (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(X ⊔ R)))
    have h2 : (QuotientGroup.mk ((⟨y, Subgroup.mem_sup_left hy⟩ : ↥(X ⊔ R)) *
        ⟨x, Subgroup.mem_sup_left hx⟩) : ↥(X ⊔ R) ⧸ R.subgroupOf (X ⊔ R)) =
        QuotientGroup.mk ((⟨x, Subgroup.mem_sup_left hx⟩ : ↥(X ⊔ R)) *
          ⟨y, Subgroup.mem_sup_left hy⟩) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact h1.eq.symm
    have h3 := QuotientGroup.eq.1 h2
    rw [Subgroup.mem_subgroupOf] at h3
    have h4 : (x * y) ∈ normalizer (R : Set Q) :=
      Subgroup.mul_mem _ (hXR hx) (hXR hy)
    have h5 := (Subgroup.mem_normalizer_iff.1 h4 _).1 h3
    have h6 : x * y * (((⟨y, Subgroup.mem_sup_left hy⟩ : ↥(X ⊔ R)) *
        ⟨x, Subgroup.mem_sup_left hx⟩)⁻¹ * ((⟨x, Subgroup.mem_sup_left hx⟩ : ↥(X ⊔ R)) *
          ⟨y, Subgroup.mem_sup_left hy⟩) : ↥(X ⊔ R)).1 * (x * y)⁻¹ = ⁅x, y⁆ := by
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h6] at h5
    exact h5

end CFSG.LocalAnalysis.WeakClosure81

end
