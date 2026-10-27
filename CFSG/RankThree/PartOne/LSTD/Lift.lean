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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.RankThree.PartOne.LSTD

open scoped commutatorElement

variable {Γ P : Type} [Group Γ] [Group P]

theorem commutatorElement_mul_central_right (h z k : Γ) (hz : z ∈ Subgroup.center Γ) :
    ⁅h * z, k⁆ = ⁅h, k⁆ := by
  have hzk : z * k * z⁻¹ = k := by
    rw [← Subgroup.mem_center_iff.mp hz k, mul_inv_cancel_right]
  calc ⁅h * z, k⁆ = h * (z * k * z⁻¹) * h⁻¹ * k⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅h, k⁆ := by rw [hzk]; rfl

theorem commutatorElement_mul_central_left (h k z : Γ) (hz : z ∈ Subgroup.center Γ) :
    ⁅h, k * z⁆ = ⁅h, k⁆ := by
  have hzh : z * h⁻¹ * z⁻¹ = h⁻¹ := by
    rw [← Subgroup.mem_center_iff.mp hz h⁻¹, mul_inv_cancel_right]
  calc ⁅h, k * z⁆ = h * k * (z * h⁻¹ * z⁻¹) * k⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅h, k⁆ := by rw [hzh]; rfl

theorem exists_lift_perfect_centralizer (π : Γ →* P) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Γ) (b : Γ) (X : Subgroup P) (hX : Group.IsPerfect X)
    (hXc : X ≤ Subgroup.centralizer ({π b} : Set P)) :
    ∃ H : Subgroup Γ, Group.IsPerfect H ∧ H.map π = X ∧
      H ≤ Subgroup.centralizer ({b} : Set Γ) := by
  set Xh : Subgroup Γ := X.comap π with hXh
  set ψ : Γ → Γ := fun g => g * b * g⁻¹ * b⁻¹ with hψ
  have hψmem : ∀ g ∈ Xh, ψ g ∈ Subgroup.center Γ := by
    intro g hg
    apply hker
    rw [MonoidHom.mem_ker]
    have h1 : π g * π b = π b * π g := Subgroup.mem_centralizer_singleton_iff.mp (hXc hg)
    simp only [hψ, map_mul, map_inv]
    rw [h1]
    group
  have hψmul : ∀ g ∈ Xh, ∀ g' ∈ Xh, ψ (g * g') = ψ g * ψ g' := by
    intro g hg g' hg'
    have hc' := hψmem g' hg'
    have hc := hψmem g hg
    have h1 : g' * b * g'⁻¹ = ψ g' * b := by simp [hψ]
    calc ψ (g * g') = g * (g' * b * g'⁻¹) * g⁻¹ * b⁻¹ := by simp only [hψ]; group
      _ = g * (ψ g' * b) * g⁻¹ * b⁻¹ := by rw [h1]
      _ = ψ g' * (g * b * g⁻¹ * b⁻¹) := by
          have := Subgroup.mem_center_iff.mp hc' g
          calc g * (ψ g' * b) * g⁻¹ * b⁻¹ = (g * ψ g') * b * g⁻¹ * b⁻¹ := by group
            _ = (ψ g' * g) * b * g⁻¹ * b⁻¹ := by rw [this]
            _ = ψ g' * (g * b * g⁻¹ * b⁻¹) := by group
      _ = ψ g * ψ g' := by
          have := Subgroup.mem_center_iff.mp hc' (ψ g)
          rw [← this]
  let ψh : ↥Xh →* ↥(Subgroup.center Γ) :=
    { toFun := fun g => ⟨ψ g, hψmem g g.2⟩
      map_one' := by
        apply Subtype.ext
        simp [hψ]
      map_mul' := fun g g' => Subtype.ext (hψmul g g.2 g' g'.2) }
  have hcomm : ∀ g ∈ Xh, ∀ g' ∈ Xh, ⁅g, g'⁆ ∈ Subgroup.centralizer ({b} : Set Γ) := by
    intro g hg g' hg'
    have h1 : ψh ⁅(⟨g, hg⟩ : ↥Xh), ⟨g', hg'⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hψmem g' hg') (ψ g))
    have h2 := congrArg Subtype.val h1
    have h3 : ψ ⁅g, g'⁆ = 1 := h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [hψ] at h3
    rw [mul_inv_eq_one] at h3
    calc ⁅g, g'⁆ * b = (⁅g, g'⁆ * b * ⁅g, g'⁆⁻¹) * ⁅g, g'⁆ := by group
      _ = b * ⁅g, g'⁆ := by rw [h3]
  refine ⟨⁅Xh, Xh⁆, ?_, ?_, Subgroup.commutator_le.mpr hcomm⟩
  ·
    have himg : (⁅Xh, Xh⁆).map π = X := by
      rw [Subgroup.map_commutator, hXh, Subgroup.map_comap_eq_self_of_surjective hπ]
      exact Subgroup.commutator_eq_self
    rw [Subgroup.isPerfect_iff]
    apply le_antisymm
    · exact Subgroup.commutator_le.mpr fun g hg g' hg' =>
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hg')
          (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hg')
    · refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      have hdecomp : ∀ x ∈ Xh, ∃ h ∈ ⁅Xh, Xh⁆, ∃ z ∈ Subgroup.center Γ, x = h * z := by
        intro x hx
        have : π x ∈ (⁅Xh, Xh⁆).map π := by rw [himg]; exact hx
        obtain ⟨h, hh, hhx⟩ := this
        refine ⟨h, hh, h⁻¹ * x, hker ?_, by group⟩
        rw [MonoidHom.mem_ker, map_mul, map_inv, hhx, inv_mul_cancel]
      obtain ⟨h, hh, z, hz, rfl⟩ := hdecomp x hx
      obtain ⟨h', hh', z', hz', rfl⟩ := hdecomp y hy
      rw [commutatorElement_mul_central_right _ _ _ hz,
        commutatorElement_mul_central_left _ _ _ hz']
      exact Subgroup.commutator_mem_commutator hh hh'
  · rw [Subgroup.map_commutator, hXh, Subgroup.map_comap_eq_self_of_surjective hπ]
    exact Subgroup.commutator_eq_self

end CFSG.RankThree.PartOne.LSTD
