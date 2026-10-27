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

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup

variable {X : Type*} [Group X]

@[expose] noncomputable def autQuot : MulAut X →* MulAut (X ⧸ center X) where
  toFun φ := QuotientGroup.congr (center X) (center X) φ
    ((Subgroup.characteristic_iff_map_eq.mp (inferInstance : (center X).Characteristic)) φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem autQuot_mk (φ : MulAut X) (x : X) :
    autQuot φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := rfl

theorem autQuot_conj (x : X) :
    autQuot (MulAut.conj x) = MulAut.conj (QuotientGroup.mk x : X ⧸ center X) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y => rfl

theorem exists_conj_autQuot {ψ : MulAut (X ⧸ center X)}
    (hψ : ψ ∈ (MulAut.conj : (X ⧸ center X) →* MulAut (X ⧸ center X)).range) :
    ∃ x : X, autQuot (MulAut.conj x) = ψ := by
  obtain ⟨y, rfl⟩ := hψ
  induction y using QuotientGroup.induction_on with
  | H x => exact ⟨x, autQuot_conj x⟩

theorem autQuot_injective (hP : commutator X = ⊤) : Function.Injective (autQuot (X := X)) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have hcen : ∀ x : X, φ x * x⁻¹ ∈ center X := by
    intro x
    have h1 : autQuot φ (QuotientGroup.mk x) = QuotientGroup.mk x := by rw [hφ]; rfl
    have h2 : (QuotientGroup.mk (φ x) : X ⧸ center X) = QuotientGroup.mk x := h1
    simpa [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem).1 h2
  let f : X →* center X := MonoidHom.mk' (fun x => ⟨φ x * x⁻¹, hcen x⟩) (by
    intro x y
    apply Subtype.ext
    show φ (x * y) * (x * y)⁻¹ = (φ x * x⁻¹) * (φ y * y⁻¹)
    have hy := Subgroup.mem_center_iff.1 (hcen y)
    rw [map_mul]
    calc φ x * φ y * (x * y)⁻¹ = φ x * (φ y * y⁻¹) * x⁻¹ := by group
      _ = φ x * ((φ y * y⁻¹) * x⁻¹) := by rw [mul_assoc]
      _ = φ x * (x⁻¹ * (φ y * y⁻¹)) := by rw [← hy x⁻¹]
      _ = (φ x * x⁻¹) * (φ y * y⁻¹) := by rw [mul_assoc])
  have hker : commutator X ≤ f.ker := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext ((Subgroup.mem_center_iff.1 (f b).2) (f a : X)))
  ext x
  have hx : x ∈ f.ker := hker (hP ▸ Subgroup.mem_top x)
  have h1 : φ x * x⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  exact mul_inv_eq_one.1 h1

end CFSG.LocalAnalysis.UniquenessCase.UCK
