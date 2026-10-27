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

namespace CFSG.Sporadic.SmallOddCore

variable {G : Type*} [Group G]

theorem card_partners_conj (C : G → G → Prop)
    (hC : ∀ (φ : MulAut G) x y, C x y → C (φ x) (φ y)) (g x : G) :
    Nat.card {y // C (g * x * g⁻¹) y} = Nat.card {y // C x y} := by
  refine Nat.card_congr ⟨fun y => ⟨g⁻¹ * y.1 * g, ?_⟩, fun y => ⟨g * y.1 * g⁻¹, ?_⟩,
    fun y => ?_, fun y => ?_⟩
  · have := hC (MulAut.conj g⁻¹) _ _ y.2
    simpa [mul_assoc] using this
  · have := hC (MulAut.conj g) _ _ y.2
    simpa using this
  · ext; simp [mul_assoc]
  · ext; simp [mul_assoc]

theorem card_mulAut_le_classSize_mul [Finite G] (a b : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (C : G → G → Prop)
    (hC : ∀ (φ : MulAut G) x y, C x y → C (φ x) (φ y)) (hab : C a b)
    (hclass : ∀ φ : MulAut G, ∃ g : G, φ a = g * a * g⁻¹) :
    Nat.card (MulAut G) ≤ {x : G | ∃ g : G, x = g * a * g⁻¹}.ncard * Nat.card {y // C a y} := by
  classical
  set S := {x : G | ∃ g : G, x = g * a * g⁻¹}
  let ev : MulAut G → {p : G × G // p.1 ∈ S ∧ C p.1 p.2} := fun φ =>
    ⟨(φ a, φ b), by
      obtain ⟨g, hg⟩ := hclass φ
      exact ⟨⟨g, hg⟩, hC φ a b hab⟩⟩
  have hev : Function.Injective ev := by
    intro φ ψ h
    have hpair := congrArg (fun p => p.1) h
    simp only [ev, Prod.mk.injEq] at hpair
    have hgens : Set.EqOn (φ : G → G) ψ ({a, b} : Set G) := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hpair.1
      · exact Set.mem_singleton_iff.mp hx ▸ hpair.2
    have := MonoidHom.eq_of_eqOn_dense (f := (φ : G →* G)) (g := (ψ : G →* G)) hgen hgens
    exact MulEquiv.ext fun x => congrArg (fun f : G →* G => f x) this
  have h1 := Nat.card_le_card_of_injective ev hev
  refine h1.trans (le_of_eq ?_)
  let e : {p : G × G // p.1 ∈ S ∧ C p.1 p.2} ≃ Σ x : S, {y // C x.1 y} :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
      invFun := fun q => ⟨(q.1.1, q.2.1), q.1.2, q.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfin : Finite S := Set.toFinite _ |>.to_subtype
  have : Fintype S := Fintype.ofFinite S
  rw [Nat.card_congr e, Nat.card_sigma]
  have hconst : ∀ x : S, Nat.card {y // C x.1 y} = Nat.card {y // C a y} := by
    rintro ⟨x, g, rfl⟩
    exact card_partners_conj C hC g a
  rw [Finset.sum_congr rfl (fun x _ => hconst x), Finset.sum_const, smul_eq_mul,
    Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

end CFSG.Sporadic.SmallOddCore
