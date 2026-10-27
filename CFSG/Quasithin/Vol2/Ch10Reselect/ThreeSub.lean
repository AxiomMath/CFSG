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

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open scoped commutatorElement

private theorem three_sub_comm_aux {G : Type*} [Group G] {c d v l : G}
    (hcv : c * v = v * c) (hvd : v * d = d * v) (hcd : c * d = d * c) (hcl : c * l = l * c)
    (hdX : d * ⁅v, l⁆ = ⁅v, l⁆ * d) :
    c * v * (d * l) * (c * v)⁻¹ * (d * l)⁻¹ = ⁅v, l⁆ := by
  have h1 : c * v * d = d * (c * v) := by
    calc c * v * d = c * (v * d) := mul_assoc _ _ _
      _ = c * (d * v) := by rw [hvd]
      _ = c * d * v := (mul_assoc _ _ _).symm
      _ = d * c * v := by rw [hcd]
      _ = d * (c * v) := mul_assoc _ _ _
  have h2 : c * v * l * (c * v)⁻¹ * l⁻¹ = ⁅v, l⁆ := by
    have e1 : c * v * l = v * l * c := by
      calc c * v * l = v * c * l := by rw [hcv]
        _ = v * (c * l) := mul_assoc _ _ _
        _ = v * (l * c) := by rw [hcl]
        _ = v * l * c := (mul_assoc _ _ _).symm
    have e2 : c * v⁻¹ = v⁻¹ * c := (Commute.inv_right (show Commute c v from hcv)).eq
    have e3 : c * (v⁻¹ * c⁻¹) = v⁻¹ := by
      calc c * (v⁻¹ * c⁻¹) = c * v⁻¹ * c⁻¹ := (mul_assoc _ _ _).symm
        _ = v⁻¹ * c * c⁻¹ := by rw [e2]
        _ = v⁻¹ := mul_inv_cancel_right _ _
    calc c * v * l * (c * v)⁻¹ * l⁻¹ = v * l * c * (v⁻¹ * c⁻¹) * l⁻¹ := by
          rw [e1, mul_inv_rev]
      _ = v * l * (c * (v⁻¹ * c⁻¹)) * l⁻¹ := by simp only [mul_assoc]
      _ = v * l * v⁻¹ * l⁻¹ := by rw [e3]
      _ = ⁅v, l⁆ := by rw [commutatorElement_def]
  calc c * v * (d * l) * (c * v)⁻¹ * (d * l)⁻¹
      = c * v * d * l * (c * v)⁻¹ * l⁻¹ * d⁻¹ := by group
    _ = d * (c * v) * l * (c * v)⁻¹ * l⁻¹ * d⁻¹ := by rw [h1]
    _ = d * (c * v * l * (c * v)⁻¹ * l⁻¹) * d⁻¹ := by group
    _ = d * ⁅v, l⁆ * d⁻¹ := by rw [h2]
    _ = ⁅v, l⁆ * d * d⁻¹ := by rw [hdX]
    _ = ⁅v, l⁆ := mul_inv_cancel_right _ _

theorem mem_centralizer_of_trivial_mod {G : Type*} [Group G] {A L0 C : Subgroup G}
    [IsMulCommutative ↥A] (hL0 : L0 ≤ Subgroup.normalizer (A : Set G)) (hcomm : A = ⁅A, L0⁆)
    (hCA : C ≤ A) (hCL : C ≤ Subgroup.centralizer (L0 : Set G)) {k : G}
    (h1 : ∀ l ∈ L0, ⁅k, l⁆ ∈ Subgroup.centralizer (A : Set G)) (h2 : ∀ v ∈ A, ⁅k, v⁆ ∈ C) :
    k ∈ Subgroup.centralizer (A : Set G) := by
  have key : ∀ v ∈ A, ∀ l ∈ L0, ⁅v, l⁆ ∈ Subgroup.centralizer ({k} : Set G) := by
    intro v hv l hl
    have hcC : ⁅k, v⁆ ∈ C := h2 v hv
    have hcA : ⁅k, v⁆ ∈ A := hCA hcC
    have hdA : ∀ a ∈ A, a * ⁅k, l⁆ = ⁅k, l⁆ * a := fun a ha =>
      Subgroup.mem_centralizer_iff.mp (h1 l hl) a ha
    have hX : ⁅v, l⁆ ∈ A := by
      have hlv : l * v⁻¹ * l⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hL0 hl) v⁻¹).mp (A.inv_mem hv)
      have hXeq : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
        rw [commutatorElement_def]
        simp only [mul_assoc]
      rw [hXeq]
      exact A.mul_mem hv hlv
    have hcv : ⁅k, v⁆ * v = v * ⁅k, v⁆ := by
      have := IsMulCommutative.is_comm.comm (⟨⁅k, v⁆, hcA⟩ : ↥A) ⟨v, hv⟩
      exact congrArg Subtype.val this
    have hcl : ⁅k, v⁆ * l = l * ⁅k, v⁆ :=
      (Subgroup.mem_centralizer_iff.mp (hCL hcC) l hl).symm
    have hvd : v * ⁅k, l⁆ = ⁅k, l⁆ * v := hdA v hv
    have hcd : ⁅k, v⁆ * ⁅k, l⁆ = ⁅k, l⁆ * ⁅k, v⁆ := hdA _ hcA
    have hdX : ⁅k, l⁆ * ⁅v, l⁆ = ⁅v, l⁆ * ⁅k, l⁆ := (hdA _ hX).symm
    have hkv : k * v * k⁻¹ = ⁅k, v⁆ * v := by
      rw [commutatorElement_def]
      group
    have hkl : k * l * k⁻¹ = ⁅k, l⁆ * l := by
      rw [commutatorElement_def]
      group
    have hconj : k * ⁅v, l⁆ * k⁻¹ = ⁅v, l⁆ := by
      calc k * ⁅v, l⁆ * k⁻¹
          = (k * v * k⁻¹) * (k * l * k⁻¹) * (k * v * k⁻¹)⁻¹ * (k * l * k⁻¹)⁻¹ := by
            rw [commutatorElement_def]
            group
        _ = ⁅k, v⁆ * v * (⁅k, l⁆ * l) * (⁅k, v⁆ * v)⁻¹ * (⁅k, l⁆ * l)⁻¹ := by
            rw [hkv, hkl]
        _ = ⁅v, l⁆ := three_sub_comm_aux hcv hvd hcd hcl hdX
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hle : ⁅A, L0⁆ ≤ Subgroup.centralizer ({k} : Set G) :=
    Subgroup.commutator_le.mpr key
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have haA : a ∈ ⁅A, L0⁆ := by
    rw [← hcomm]
    exact ha
  exact (Subgroup.mem_centralizer_iff.mp (hle haA) k (Set.mem_singleton k)).symm

end CFSG.Quasithin.Vol2.Ch10Reselect
