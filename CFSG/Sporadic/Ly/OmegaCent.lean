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

namespace CFSG.Sporadic.Ly.Omega

open MulAction

variable {G : Type*} [Group G]

theorem card_mul_card_centralizer_le [Finite G] (y t : G) (hyt : ∀ h : G, Commute h y → Commute h t)
    (S : Set G) (hS : ∀ z ∈ S, ∃ h : G, Commute h t ∧ z = h * y * h⁻¹) :
    S.ncard * Nat.card (Subgroup.centralizer ({y} : Set G)) ≤
      Nat.card (Subgroup.centralizer ({t} : Set G)) := by
  classical
  have hz : ∀ z : S, ∃ h : G, Commute h t ∧ z.1 = h * y * h⁻¹ := fun z => hS z.1 z.2
  choose hh hht hhz using hz
  let f : S × Subgroup.centralizer ({y} : Set G) → Subgroup.centralizer ({t} : Set G) :=
    fun q => ⟨hh q.1 * q.2.1, by
      have hc : Commute q.2.1 t := hyt _ (Subgroup.mem_centralizer_singleton_iff.1 q.2.2)
      exact Subgroup.mem_centralizer_singleton_iff.2 ((hht q.1).mul_left hc).eq⟩
  have hf : Function.Injective f := by
    rintro ⟨z, c⟩ ⟨z', c'⟩ e
    have e1 : hh z * c.1 = hh z' * c'.1 := congrArg Subtype.val e
    have hcy : ∀ c : Subgroup.centralizer ({y} : Set G), c.1 * y * c.1⁻¹ = y := by
      intro c
      rw [Subgroup.mem_centralizer_singleton_iff.1 c.2, mul_inv_cancel_right]
    have k : ∀ (a : G) (c : Subgroup.centralizer ({y} : Set G)),
        (a * c.1) * y * (a * c.1)⁻¹ = a * y * a⁻¹ := by
      intro a c
      calc (a * c.1) * y * (a * c.1)⁻¹ = a * (c.1 * y * c.1⁻¹) * a⁻¹ := by group
        _ = a * y * a⁻¹ := by rw [hcy c]
    have e2 : z.1 = z'.1 := by
      rw [hhz z, hhz z', ← k (hh z) c, ← k (hh z') c', e1]
    have hzz : z = z' := Subtype.ext e2
    subst hzz
    have hcc : c = c' := Subtype.ext (mul_left_cancel e1)
    rw [hcc]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_coe_set_eq] at this

theorem card_centralizer_conj (c t : G) :
    Nat.card (Subgroup.centralizer ({c * t * c⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({t} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun h => ⟨c⁻¹ * h.1 * c, ?_⟩
      invFun := fun h => ⟨c * h.1 * c⁻¹, ?_⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc]) }
  · obtain ⟨h, hh⟩ := h
    rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
    have e : c⁻¹ * (h * (c * t * c⁻¹)) * c = c⁻¹ * ((c * t * c⁻¹) * h) * c := by rw [hh]
    calc c⁻¹ * h * c * t = c⁻¹ * (h * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * h) * c := e
      _ = t * (c⁻¹ * h * c) := by group
  · obtain ⟨h, hh⟩ := h
    rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
    calc c * h * c⁻¹ * (c * t * c⁻¹) = c * (h * t) * c⁻¹ := by group
      _ = c * (t * h) * c⁻¹ := by rw [hh]
      _ = c * t * c⁻¹ * (c * h * c⁻¹) := by group

theorem card_centralizer_le_of_orbit [Finite G] (t : G) {n m : ℕ}
    (hn : n ≤ Nat.card (orbit (ConjAct G) t)) (hG : Nat.card G ≤ n * m) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) ≤ m := by
  have hos : Nat.card (stabilizer (ConjAct G) t) * Nat.card (orbit (ConjAct G) t) = Nat.card G := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) t)
    rw [Nat.card_prod, ← Nat.card_congr (ConjAct.toConjAct (G := G)).toEquiv] at h
    rw [Nat.mul_comm]
    exact h
  have hst : Nat.card (stabilizer (ConjAct G) t) = Nat.card (Subgroup.centralizer ({t} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨ConjAct.ofConjAct g.1, ?_⟩
        invFun := fun g => ⟨ConjAct.toConjAct g.1, ?_⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    · obtain ⟨g, hg⟩ := g
      rw [mem_stabilizer_iff, ConjAct.smul_def, mul_inv_eq_iff_eq_mul] at hg
      exact Subgroup.mem_centralizer_singleton_iff.2 hg
    · obtain ⟨g, hg⟩ := g
      rw [mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 hg
  rw [hst] at hos
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, zero_mul] at hG
      have := Nat.card_pos (α := G)
      omega
    · exact h
  by_contra hc
  push Not at hc
  have : n * m < n * m :=
    calc n * m < n * Nat.card (Subgroup.centralizer ({t} : Set G)) := Nat.mul_lt_mul_of_pos_left hc hn0
      _ ≤ Nat.card (orbit (ConjAct G) t) * Nat.card (Subgroup.centralizer ({t} : Set G)) :=
        Nat.mul_le_mul_right _ hn
      _ = Nat.card G := by rw [Nat.mul_comm]; exact hos
      _ ≤ n * m := hG
  exact lt_irrefl _ this

end CFSG.Sporadic.Ly.Omega

end
