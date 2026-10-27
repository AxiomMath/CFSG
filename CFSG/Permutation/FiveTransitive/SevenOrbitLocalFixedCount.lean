module

public import CFSG.Permutation.FiveTransitive.Degree54SevenOrbitFiveFixed
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily
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
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG

namespace FiveTransitive.SevenOrbitLocalFixedCount
open MulAction FixedNormalizerAction NormalizerOrbitFamily

theorem local_add_seven_mul_fixed_labels_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P) (hQ : IsPGroup 7 Q)
    (g : Normalizer Q) (hg : g ^ 5 = 1) :
    Nat.card (Function.fixedPoints (toPermHom (Normalizer Q) (Fixed (X := X) Q) g)) +
    7 * Nat.card (Function.fixedPoints (NormalizerOrbitFamily.toPermHom (X := X) Q 7 g)) ≤
      Nat.card (Function.fixedPoints g.val.val) := by
  classical
  let C := Function.fixedPoints (NormalizerOrbitFamily.toPermHom (X := X) Q 7 g)
  let e (c : C) : Fin 7 ↪ c.val.val.orbit :=
    (Fin.castLEEmb c.val.property.ge).trans (Finite.equivFin c.val.val.orbit).symm.toEmbedding
  have hfixed (c : C) (y : c.val.val.orbit) : g.val • y.val = y.val := by
    have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g c.val.val = c.val.val :=
      congrArg Subtype.val c.property
    have he : (Quotient.mk'' y.val : orbitRel.Quotient Q X) = c.val.val :=
      orbitRel.Quotient.mem_orbit.mp y.property
    have hsize : Nat.card (orbit Q y.val) = 7 := by
      rw [← orbitRel.Quotient.orbit_mk,he]
      exact c.val.property
    have hgy : g.val • y.val ∈ orbit Q y.val := by
      apply Quotient.exact (s := orbitRel Q X)
      change NormalizerOrbitHom.toPermHom (Y := X) Q g (Quotient.mk'' y.val) = Quotient.mk'' y.val
      rwa [he]
    exact Degree54SevenOrbitFiveFixed.fixes_preserved_orbit Q hQ g.val g.property
      (congrArg Subtype.val hg) y.val (by rw [hsize]; decide) hgy y.val (mem_orbit_self y.val)
  let f : C × Fin 7 → Function.fixedPoints g.val.val :=
    fun z => ⟨(e z.1 z.2).val,hfixed z.1 (e z.1 z.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : (e a.1 a.2).val = (e b.1 b.2).val := congrArg Subtype.val hab
    have ha : (Quotient.mk'' (e a.1 a.2).val : orbitRel.Quotient Q X) = a.1.val.val :=
      orbitRel.Quotient.mem_orbit.mp (e a.1 a.2).property
    have hb : (Quotient.mk'' (e b.1 b.2).val : orbitRel.Quotient Q X) = b.1.val.val :=
      orbitRel.Quotient.mem_orbit.mp (e b.1 b.2).property
    have hc : a.1 = b.1 := Subtype.ext (Subtype.ext (ha.symm.trans ((congrArg Quotient.mk'' hab').trans hb)))
    rcases a with ⟨a,i⟩
    rcases b with ⟨b,j⟩
    dsimp only at hc
    subst b
    have hij : i = j := (e a).injective (Subtype.ext hab')
    subst j
    rfl
  let D := Function.fixedPoints (toPermHom (Normalizer Q) (Fixed (X := X) Q) g)
  let d : D → Function.fixedPoints g.val.val := fun x =>
    ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hd : Function.Injective d := by
    intro x y he
    have hv : x.val.val = y.val.val := congrArg (fun z : Function.fixedPoints g.val.val => z.val) he
    exact Subtype.ext (Subtype.ext hv)
  have hdis (x : D) (z : C × Fin 7) : d x ≠ f z := by
    intro he
    have hv : x.val.val = (e z.1 z.2).val := congrArg Subtype.val he
    have hx : x.val.val ∈ fixedPoints Q X := by
      rw [← fixed_eq Q]
      exact x.val.property
    have horb : Nat.card (orbit Q (e z.1 z.2).val) = 1 := by
      rw [Nat.card_eq_fintype_card]
      apply mem_fixedPoints_iff_card_orbit_eq_one.mp
      rwa [← hv]
    have heq : (Quotient.mk'' (e z.1 z.2).val : orbitRel.Quotient Q X) = z.1.val.val :=
      orbitRel.Quotient.mem_orbit.mp (e z.1 z.2).property
    rw [← orbitRel.Quotient.orbit_mk,heq,z.1.val.property] at horb
    omega
  let j : D ⊕ (C × Fin 7) → Function.fixedPoints g.val.val := Sum.elim d f
  have hj : Function.Injective j := by
    intro a b he
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (hd he)
      | inr b => exact False.elim (hdis a b he)
    | inr a =>
      cases b with
      | inl b => exact False.elim (hdis b a he.symm)
      | inr b => exact congrArg Sum.inr (hf he)
  have hh := Nat.card_le_card_of_injective j hj
  rw [Nat.card_sum,Nat.card_prod,Nat.card_fin] at hh
  simpa only [Nat.mul_comm] using hh

end FiveTransitive.SevenOrbitLocalFixedCount

end CFSG
