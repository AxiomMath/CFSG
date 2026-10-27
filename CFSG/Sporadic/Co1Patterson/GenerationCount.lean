module

public import CFSG.Sporadic.Co1.Module.OddCount
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Co1Patterson

open Subgroup

theorem ncard_fixed_mul_card {X : Type*} [Group X] [Finite X] (Y : Subgroup X) (t : X) :
    {q : X ⧸ Y | t • q = q}.ncard * Nat.card Y =
      Nat.card (centralizer ({t} : Set X)) * {y : Y | IsConj t (y : X)}.ncard := by
  have h := CFSG.Sporadic.Co1.Module.Odd.card_centralizer_mul_ncard_conj_inter t
    ((1 : X) : X ⧸ Y)
  rw [MulAction.stabilizer_quotient, MulAction.orbit_eq_univ] at h
  have e1 : {x : X | x ∈ Y ∧ IsConj t x} = Subtype.val '' {y : Y | IsConj t (y : X)} := by
    ext x
    constructor
    · rintro ⟨hx, hc⟩
      exact ⟨⟨x, hx⟩, hc, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  have e2 : {q : X ⧸ Y | q ∈ Set.univ ∧ t • q = q} = {q : X ⧸ Y | t • q = q} := by
    ext q
    simp
  rw [e1, Set.ncard_image_of_injective _ Subtype.val_injective, e2] at h
  rw [mul_comm]
  exact h.symm

theorem ncard_isConj_mul_card_centralizer {G : Type*} [Group G] [Finite G] (a : G) :
    {y : G | IsConj a y}.ncard * Nat.card (centralizer ({a} : Set G)) = Nat.card G := by
  have h := CFSG.Sporadic.Co1.Module.Odd.card_centralizer_mul_ncard_conj_inter (Ω := Unit) a ()
  have hs : MulAction.stabilizer G () = ⊤ :=
    eq_top_iff.mpr fun g _ => Subsingleton.elim _ _
  have e1 : {y : G | y ∈ MulAction.stabilizer G () ∧ IsConj a y} =
      {y : G | IsConj a y} := by
    ext y
    simp
  have e2 : {ω : Unit | ω ∈ MulAction.orbit G () ∧ a • ω = ω} = Set.univ :=
    Set.eq_univ_of_forall fun ω => ⟨Subsingleton.elim ω () ▸ MulAction.mem_orbit_self _,
      Subsingleton.elim _ _⟩
  rw [e1, e2, hs, Subgroup.card_top, Set.ncard_univ, Nat.card_unique (α := Unit), mul_one] at h
  rw [mul_comm]
  exact h

theorem map_centralizer_subtype {G : Type*} [Group G] (H : Subgroup G) (x : H) :
    (centralizer ({x} : Set H)).map H.subtype = H ⊓ centralizer {(x : G)} := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨g.2, mem_centralizer_singleton_iff.mpr ?_⟩
    have := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hg)
    simpa using this
  · intro hg
    obtain ⟨hgH, hgC⟩ := Subgroup.mem_inf.mp hg
    refine ⟨⟨g, hgH⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
    simpa using mem_centralizer_singleton_iff.mp hgC

section Classes

variable {G : Type*} [Group G] (P : G → Prop)

theorem setOf_and_isConj_eq (hP : ∀ g x : G, P x → P (g * x * g⁻¹)) {r : G} (hr : P r) :
    {x | P x ∧ IsConj r x} = {x | IsConj r x} := by
  ext x
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact hP g r hr

theorem setOf_and_isConj_eq_empty (hP : ∀ g x : G, P x → P (g * x * g⁻¹)) {r : G} (hr : ¬ P r) :
    {x | P x ∧ IsConj r x} = ∅ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx h
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  apply hr
  have := hP g⁻¹ _ hx
  rwa [show g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r by group] at this

theorem ncard_setOf_eq_add [Finite G] {a b c : G}
    (hcls : ∀ x, P x → IsConj a x ∨ IsConj b x ∨ IsConj c x)
    (hab : ¬ IsConj a b) (hac : ¬ IsConj a c) (hbc : ¬ IsConj b c) :
    {x | P x}.ncard = {x | P x ∧ IsConj a x}.ncard + {x | P x ∧ IsConj b x}.ncard +
      {x | P x ∧ IsConj c x}.ncard := by
  have hdisj : ∀ {r s : G}, ¬ IsConj r s →
      Disjoint {x | P x ∧ IsConj r x} {x | P x ∧ IsConj s x} := by
    intro r s hrs
    rw [Set.disjoint_left]
    rintro x ⟨-, hr⟩ ⟨-, hs⟩
    exact hrs (hr.trans hs.symm)
  have hU : {x | P x} = {x | P x ∧ IsConj a x} ∪ {x | P x ∧ IsConj b x} ∪
      {x | P x ∧ IsConj c x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hx
      rcases hcls x hx with h | h | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · exact Or.inl (Or.inr ⟨hx, h⟩)
      · exact Or.inr ⟨hx, h⟩
    · rintro ((h | h) | h) <;> exact h.1
  rw [hU, Set.ncard_union_eq, Set.ncard_union_eq (hdisj hab)]
  rw [Set.disjoint_union_left]
  exact ⟨hdisj hac, hdisj hbc⟩

end Classes

theorem ncard_fixed_eq_one_of_classes {X : Type*} [Group X] [Finite X] {t : X}
    (ht : orderOf t = 2) (hC : Nat.card (centralizer ({t} : Set X)) = 89181388800)
    {Y : Subgroup X} (hY : Nat.card Y = 4157776806543360000) (htY : t ∈ Y) {a b c : Y}
    (hcls : ∀ y : Y, orderOf y = 2 → IsConj a y ∨ IsConj b y ∨ IsConj c y)
    (hab : ¬ IsConj a b) (hac : ¬ IsConj a c) (hbc : ¬ IsConj b c)
    (hCa : Nat.card (centralizer ({a} : Set Y)) = 89181388800)
    (hCb : Nat.card (centralizer ({b} : Set Y)) = 2012774400)
    (hCc : Nat.card (centralizer ({c} : Set Y)) = 389283840) :
    {q : X ⧸ Y | t • q = q}.ncard = 1 ∧ IsConj t (a : X) ∧ ¬ IsConj t (b : X) ∧
      ¬ IsConj t (c : X) := by
  have hP : ∀ g x : Y, IsConj t (x : X) → IsConj t ((g * x * g⁻¹ : Y) : X) := fun g x hx =>
    hx.trans (isConj_iff.mpr ⟨(g : X), by simp⟩)
  have hcov : ∀ x : Y, IsConj t (x : X) → IsConj a x ∨ IsConj b x ∨ IsConj c x := by
    intro x hx
    apply hcls
    obtain ⟨g, hg⟩ := isConj_iff.mp hx
    rw [← Subgroup.orderOf_coe, ← hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  have hsum := ncard_setOf_eq_add (fun y : Y => IsConj t (y : X)) hcov hab hac hbc
  have hsplit : ∀ r : Y,
      ({x : Y | IsConj t (x : X) ∧ IsConj r x}.ncard = {x : Y | IsConj r x}.ncard ∧
        IsConj t (r : X)) ∨
      ({x : Y | IsConj t (x : X) ∧ IsConj r x}.ncard = 0 ∧ ¬ IsConj t (r : X)) := by
    intro r
    by_cases hr : IsConj t (r : X)
    · exact Or.inl ⟨by rw [setOf_and_isConj_eq (fun y : Y => IsConj t (y : X)) hP hr], hr⟩
    · refine Or.inr ⟨?_, hr⟩
      rw [setOf_and_isConj_eq_empty (fun y : Y => IsConj t (y : X)) hP hr, Set.ncard_empty]
  have hKa := ncard_isConj_mul_card_centralizer a
  have hKb := ncard_isConj_mul_card_centralizer b
  have hKc := ncard_isConj_mul_card_centralizer c
  rw [hCa, hY] at hKa
  rw [hCb, hY] at hKb
  rw [hCc, hY] at hKc
  have hfix := ncard_fixed_mul_card Y t
  rw [hY, hC] at hfix
  have hpos : 0 < {y : Y | IsConj t (y : X)}.ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨⟨t, htY⟩, IsConj.refl t⟩
  rcases hsplit a with ⟨ha, hPa⟩ | ⟨ha, hPa⟩ <;> rcases hsplit b with ⟨hb, hPb⟩ | ⟨hb, hPb⟩ <;>
    rcases hsplit c with ⟨hc, hPc⟩ | ⟨hc, hPc⟩
  all_goals first
    | exact ⟨by omega, hPa, hPb, hPc⟩
    | exact absurd hfix (by omega)

end CFSG.Sporadic.Co1Patterson
