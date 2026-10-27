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

namespace CFSG.Sporadic.Recognition.JankoWong

theorem eq_of_abelian_of_card_eighty_one {G : Type*} [Group G] {W N N' : Subgroup G}
    (hW : Nat.card W = 3 ^ 6) (hN : Nat.card N = 81) (hN' : Nat.card N' = 81)
    (hNW : N ≤ W) (hN'W : N' ≤ W)
    (hNab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hN'ab : ∀ x ∈ N', ∀ y ∈ N', x * y = y * x)
    (hcent : ∀ x ∈ W, x ∉ N → Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 9)
    (hZ : ∀ D : Subgroup G, D ≤ W → (∀ y ∈ D, ∀ w ∈ W, w * y = y * w) → Nat.card D ≤ 3) :
    N = N' := by
  by_contra hne
  have hfN : Finite N := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  have hfW : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  have hN'N : ¬ N' ≤ N := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge h (by rw [hN, hN'])).symm
  obtain ⟨x, hxN', hxN⟩ := IsConcreteLE.not_le_iff_exists.mp hN'N
  have hSW : N ⊔ N' ≤ W := sup_le hNW hN'W
  have hSdvd : Nat.card ↥(N ⊔ N') ∣ 3 ^ 6 := by
    rw [← hW]
    exact Subgroup.card_dvd_of_le hSW
  have hSpos : 0 < Nat.card ↥(N ⊔ N') := Nat.pos_of_dvd_of_pos hSdvd (by norm_num)
  have hSle : Nat.card ↥(N ⊔ N') ≤ 3 ^ 6 := Nat.le_of_dvd (by norm_num) hSdvd
  have e1 : N.relIndex N' * Nat.card ↥(N ⊓ N') = 81 := by
    rw [Subgroup.relIndex_mul_card, hN']
  have e2 : N.relIndex (N ⊔ N') * 81 = Nat.card ↥(N ⊔ N') := by
    have := Subgroup.relIndex_mul_card N (N ⊔ N')
    rwa [inf_eq_left.mpr le_sup_left, hN] at this
  have hne0 : N.relIndex (N ⊔ N') ≠ 0 := by
    intro h
    rw [h] at e2
    omega
  have hle : N.relIndex N' ≤ N.relIndex (N ⊔ N') :=
    Subgroup.relIndex_le_of_le_right le_sup_right hne0
  have hr1 : N.relIndex N' ≠ 1 := fun h => hN'N (Subgroup.relIndex_eq_one.mp h)
  have hr0 : N.relIndex N' ≠ 0 := by
    intro h
    rw [h] at e1
    omega
  have hr9 : N.relIndex N' ≤ 9 := by omega
  have hcases : N.relIndex N' = 3 ∨ N.relIndex N' = 9 := by
    have key : ∀ r c : ℕ, r * c = 81 → r ≠ 0 → r ≠ 1 → r ≤ 9 → r = 3 ∨ r = 9 := by
      intro r c h h0 h1 h9
      interval_cases r <;> omega
    exact key _ _ e1 hr0 hr1 hr9
  rcases hcases with h3 | h9
  · have hc27 : Nat.card ↥(N ⊓ N') = 27 := by
      rw [h3] at e1
      omega
    have hsub : N ⊓ N' ≤ N ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine le_inf inf_le_left (fun y hy => ?_)
      obtain ⟨_, hy2⟩ := Subgroup.mem_inf.mp hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hN'ab _ hxN' _ hy2
    have : Finite ↥(N ⊓ Subgroup.centralizer ({x} : Set G)) :=
      Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
    have h1 := Subgroup.card_le_of_le hsub
    have h2 := hcent x (hN'W hxN') hxN
    omega
  · have hc9 : Nat.card ↥(N ⊓ N') = 9 := by
      rw [h9] at e1
      omega
    have hSeq : N ⊔ N' = W := by
      refine Subgroup.eq_of_le_of_card_ge hSW ?_
      rw [hW]
      omega
    have hDW : N ⊓ N' ≤ W := inf_le_left.trans hNW
    have hcomm : ∀ y ∈ N ⊓ N', ∀ w ∈ W, w * y = y * w := by
      intro y hy w hw
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      have hle' : N ⊔ N' ≤ Subgroup.centralizer ({y} : Set G) := by
        refine sup_le (fun a ha => ?_) (fun a ha => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact hNab _ hy1 _ ha
        · rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact hN'ab _ hy2 _ ha
      exact ((Subgroup.mem_centralizer_iff.mp (hle' (hSeq.ge hw))) y rfl).symm
    have h1 := hZ _ hDW hcomm
    omega

end CFSG.Sporadic.Recognition.JankoWong
