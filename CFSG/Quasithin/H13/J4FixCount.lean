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

namespace CFSG.Quasithin.H13.J4

open MulAction

theorem card_eq_card_image_mul {α β : Type*} [Finite α] (f : α → β) (S : Set β)
    (hS : ∀ b, b ∈ S ↔ ∃ a, f a = b) (m : ℕ) (hm : ∀ b ∈ S, Nat.card {a // f a = b} = m) :
    Nat.card α = Nat.card S * m := by
  classical
  have hfin : Finite S := by
    have : S = Set.range f := Set.ext fun b => (hS b).trans Iff.rfl
    rw [this]; exact (Set.finite_range f).to_subtype
  have : Fintype S := Fintype.ofFinite S
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f)]
  have e : (Σ b : β, {a // f a = b}) ≃ Σ b : S, {a // f a = b} :=
    { toFun := fun p => ⟨⟨p.1, (hS _).2 ⟨p.2.1, p.2.2⟩⟩, p.2⟩
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfin' : ∀ b : S, Finite {a // f a = b} := fun _ => inferInstance
  rw [Nat.card_congr e, Nat.card_sigma, Finset.sum_congr rfl (fun (b : S) _ => hm b.1 b.2),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

variable {G X : Type*} [Group G] [MulAction G X] [Finite G]

omit [Finite G] in
theorem card_smul_fiber [IsPretransitive G X] (x₀ x : X) :
    Nat.card {g : G // g • x₀ = x} = Nat.card (stabilizer G x₀) := by
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq G x₀ x
  refine Nat.card_congr
    { toFun := fun g => ⟨g₀⁻¹ * g.1, by
        rw [mem_stabilizer_iff, mul_smul, g.2, inv_smul_eq_iff, hg₀]⟩
      invFun := fun h => ⟨g₀ * h.1, by rw [mul_smul, mem_stabilizer_iff.1 h.2, hg₀]⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun h => Subtype.ext (by simp) }

omit [Finite G] in
theorem card_conj_fiber (t s : G) (hs : IsConj t s) :
    Nat.card {g : G // g⁻¹ * t * g = s} = Nat.card (Subgroup.centralizer ({t} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hs
  have hc' : c⁻¹⁻¹ * t * c⁻¹ = s := by rw [inv_inv]; exact hc
  refine Nat.card_congr
    { toFun := fun g => ⟨g.1 * c, by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        rcases g with ⟨g, hg⟩
        have e : g⁻¹ * t * g = c * t * c⁻¹ := hg.trans hc.symm
        calc t * (g * c) = g * (g⁻¹ * t * g) * c := by group
          _ = g * (c * t * c⁻¹) * c := by rw [e]
          _ = g * c * t := by group⟩
      invFun := fun h => ⟨h.1 * c⁻¹, by
        have hh : t * h.1 = h.1 * t := Subgroup.mem_centralizer_iff.1 h.2 t rfl
        calc (h.1 * c⁻¹)⁻¹ * t * (h.1 * c⁻¹) = c * (h.1⁻¹ * (t * h.1)) * c⁻¹ := by group
          _ = c * t * c⁻¹ := by rw [hh]; group
          _ = s := hc⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun h => Subtype.ext (by simp) }

theorem card_fix_mul_card_stabilizer [IsPretransitive G X] (x₀ : X) (t : G) :
    Nat.card {x : X // t • x = x} * Nat.card (stabilizer G x₀) =
      Nat.card (Subgroup.centralizer ({t} : Set G)) *
        Nat.card {s : G // s ∈ stabilizer G x₀ ∧ IsConj t s} := by
  classical
  have hA : ∀ g : G, g⁻¹ * t * g ∈ stabilizer G x₀ ↔ t • (g • x₀) = g • x₀ := by
    intro g
    rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff]
  have h1 : Nat.card {g : G // g⁻¹ * t * g ∈ stabilizer G x₀} =
      Nat.card {x : X // t • x = x} * Nat.card (stabilizer G x₀) := by
    have := card_eq_card_image_mul (α := {g : G // g⁻¹ * t * g ∈ stabilizer G x₀})
      (fun g => (g.1 • x₀ : X)) {x : X | t • x = x}
      (fun b => ⟨fun hb => by
        obtain ⟨g, hg⟩ := exists_smul_eq G x₀ b
        exact ⟨⟨g, (hA g).2 (by rw [hg]; exact hb)⟩, hg⟩,
        fun ⟨g, hg⟩ => by rw [← hg]; exact (hA g.1).1 g.2⟩)
      (Nat.card (stabilizer G x₀)) (fun b hb => by
        rw [← card_smul_fiber x₀ b]
        exact Nat.card_congr
          { toFun := fun a => ⟨a.1.1, a.2⟩
            invFun := fun g => ⟨⟨g.1, (hA g.1).2 (by rw [g.2]; exact hb)⟩, g.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl })
    exact this
  have h2 : Nat.card {g : G // g⁻¹ * t * g ∈ stabilizer G x₀} =
      Nat.card {s : G // s ∈ stabilizer G x₀ ∧ IsConj t s} *
        Nat.card (Subgroup.centralizer ({t} : Set G)) := by
    have := card_eq_card_image_mul (α := {g : G // g⁻¹ * t * g ∈ stabilizer G x₀})
      (fun g => g.1⁻¹ * t * g.1) {s : G | s ∈ stabilizer G x₀ ∧ IsConj t s}
      (fun b => ⟨fun hb => by
        obtain ⟨c, hc⟩ := isConj_iff.1 hb.2
        refine ⟨⟨c⁻¹, ?_⟩, ?_⟩
        · rw [inv_inv, hc]; exact hb.1
        · show c⁻¹⁻¹ * t * c⁻¹ = b
          rw [inv_inv]; exact hc,
        fun ⟨g, hg⟩ => by
          rw [← hg]
          exact ⟨g.2, isConj_iff.2 ⟨g.1⁻¹, by rw [inv_inv]⟩⟩⟩)
      (Nat.card (Subgroup.centralizer ({t} : Set G))) (fun b hb => by
        rw [← card_conj_fiber t b hb.2]
        exact Nat.card_congr
          { toFun := fun a => ⟨a.1.1, a.2⟩
            invFun := fun g => ⟨⟨g.1, by rw [g.2]; exact hb.1⟩, g.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl })
    rw [this]
    rfl
  rw [← h1, h2, mul_comm]

end CFSG.Quasithin.H13.J4
