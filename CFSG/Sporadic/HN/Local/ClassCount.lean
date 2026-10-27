module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Action.Concrete
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

namespace CFSG.Sporadic.HN.Local

open MulAction

theorem card_conj_mul_card_centralizer {G : Type*} [Group G] [Finite G] (t : G) :
    Nat.card {s : G // IsConj t s} * Nat.card (Subgroup.centralizer {t}) = Nat.card G := by
  classical
  have := Fintype.ofFinite G
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) t
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
  have e : Nat.card {s : G // IsConj t s} = Nat.card (MulAction.orbit (ConjAct G) t) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s => by
      rw [ConjAct.mem_orbit_conjAct, isConj_comm])
  rw [e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := MulAction.stabilizer (ConjAct G) t),
    Nat.card_eq_fintype_card (α := G), ← ConjAct.card]
  exact h

theorem card_fixed_of_isConj {G X : Type*} [Group G] [MulAction G X] {a b : G} (h : IsConj a b) :
    Nat.card {x : X // a • x = x} = Nat.card {x : X // b • x = x} := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  subst hc
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm c) fun x => ?_)
  show a • x = x ↔ (c * a * c⁻¹) • (c • x) = c • x
  rw [mul_smul, mul_smul, inv_smul_smul, smul_left_cancel_iff]

@[expose] def conjClassEquiv {G : Type*} [Group G] (t g : G) :
    {s : G // IsConj t s} ≃ {s : G // IsConj t s} where
  toFun s := ⟨g⁻¹ * s.1 * g, s.2.trans (isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩)⟩
  invFun s := ⟨g * s.1 * g⁻¹, s.2.trans (isConj_iff.2 ⟨g, rfl⟩)⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])

theorem card_centralizer_mul_card_inter {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [Finite X] [MulAction.IsPretransitive G X] (x₀ : X) (t : G) :
    Nat.card (Subgroup.centralizer {t}) *
        Nat.card {h : G // h ∈ MulAction.stabilizer G x₀ ∧ IsConj t h} =
      Nat.card {y : X // t • y = y} * Nat.card (MulAction.stabilizer G x₀) := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite X
  set K := MulAction.stabilizer G x₀ with hK
  set C := {s : G // IsConj t s} with hC
  have h1 := card_conj_mul_card_centralizer t
  have h4 : Nat.card X * Nat.card K = Nat.card G := by
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x₀
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card] at h
    rwa [Nat.card_congr (Equiv.subtypeUnivEquiv (p := (· ∈ MulAction.orbit G x₀)) fun y => by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x₀ y
      exact ⟨g, hg⟩)] at h
  have hQ1 : Nat.card {c : C × X // c.1.1 • c.2 = c.2} =
      Nat.card C * Nat.card {y : X // t • y = y} := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (p := fun (s : C) (y : X) => s.1 • y = y)),
      Nat.card_sigma]
    rw [Finset.sum_congr rfl fun s _ => (card_fixed_of_isConj (X := X) s.2).symm,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  have hQ2 : Nat.card {c : C × X // c.1.1 • c.2 = c.2} =
      Nat.card X * Nat.card {h : G // h ∈ K ∧ IsConj t h} := by
    rw [Nat.card_congr (Equiv.subtypeEquiv (Equiv.prodComm C X)
        (p := fun c : C × X => c.1.1 • c.2 = c.2) (q := fun c : X × C => c.2.1 • c.1 = c.1)
        fun c => Iff.rfl),
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (p := fun (y : X) (s : C) => s.1 • y = y)),
      Nat.card_sigma]
    have hconst : ∀ y : X, Nat.card {s : C // s.1 • y = y} =
        Nat.card {h : G // h ∈ K ∧ IsConj t h} := by
      intro y
      obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x₀ y
      calc Nat.card {s : C // s.1 • g • x₀ = g • x₀}
          = Nat.card {s : C // s.1 • x₀ = x₀} :=
            Nat.card_congr (Equiv.subtypeEquiv (conjClassEquiv t g) fun s => by
              show s.1 • g • x₀ = g • x₀ ↔ (g⁻¹ * s.1 * g) • x₀ = x₀
              rw [mul_smul, mul_smul, inv_smul_eq_iff])
        _ = Nat.card {h : G // h ∈ K ∧ IsConj t h} :=
            Nat.card_congr
              { toFun := fun s => ⟨s.1.1, (MulAction.mem_stabilizer_iff.2 s.2), s.1.2⟩
                invFun := fun h => ⟨⟨h.1, h.2.2⟩, MulAction.mem_stabilizer_iff.1 h.2.1⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl }
    rw [Finset.sum_congr rfl fun y _ => hconst y, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, ← Nat.card_eq_fintype_card]
  have hpos : 0 < Nat.card C := Nat.card_pos_iff.2 ⟨⟨⟨t, IsConj.refl t⟩⟩, inferInstance⟩
  have key : Nat.card C * (Nat.card (Subgroup.centralizer {t}) *
      Nat.card {h : G // h ∈ K ∧ IsConj t h}) =
      Nat.card C * (Nat.card {y : X // t • y = y} * Nat.card K) := by
    calc Nat.card C * (Nat.card (Subgroup.centralizer {t}) *
          Nat.card {h : G // h ∈ K ∧ IsConj t h})
        = Nat.card G * Nat.card {h : G // h ∈ K ∧ IsConj t h} := by rw [← h1]; ring
      _ = (Nat.card X * Nat.card K) * Nat.card {h : G // h ∈ K ∧ IsConj t h} := by rw [h4]
      _ = (Nat.card X * Nat.card {h : G // h ∈ K ∧ IsConj t h}) * Nat.card K := by ring
      _ = Nat.card {c : C × X // c.1.1 • c.2 = c.2} * Nat.card K := by rw [hQ2]
      _ = Nat.card C * (Nat.card {y : X // t • y = y} * Nat.card K) := by rw [hQ1]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos key

end CFSG.Sporadic.HN.Local
