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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.RankThree.PartOne.KCUnitary

variable {α : Type*}

theorem fix_of_card_orbits_lt {S : Set α} (hS : S.Finite) (π δ : α → α)
    (hπ : ∀ a ∈ S, π a ∈ S) (hδ : ∀ a ∈ S, δ a ∈ S) (hδδ : ∀ a ∈ S, δ (δ a) = a)
    (hcomm : ∀ a ∈ S, π (δ a) = δ (π a)) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hπk : ∀ a ∈ S, π^[p ^ k] a = a)
    (hcard : Nat.card ↥((fun a => ({a, δ a} : Set α)) '' S) < p) :
    ∀ a ∈ S, π a = a := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Ω : Set (Set α) := (fun a => ({a, δ a} : Set α)) '' S with hΩ
  have hΩfin : Ω.Finite := hS.image _
  have hmem : ∀ O ∈ Ω, π '' O ∈ Ω := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨π a, hπ a ha, ?_⟩
    simp only [Set.image_pair, hcomm a ha]
  let f : Ω → Ω := fun O => ⟨π '' O.1, hmem O.1 O.2⟩
  have hfiter : ∀ (m : ℕ) (O : Ω), (f^[m] O).1 = π^[m] '' O.1 := by
    intro m
    induction m with
    | zero => intro O; simp
    | succ m ih =>
      intro O
      rw [Function.iterate_succ_apply']
      show π '' (f^[m] O).1 = _
      rw [ih, Set.image_image]
      ext y
      simp [Function.iterate_succ_apply']
  have hfN : ∀ O : Ω, f^[p ^ k] O = O := by
    rintro ⟨_, a, ha, rfl⟩
    apply Subtype.ext
    rw [hfiter]
    simp only [Set.image_pair]
    rw [hπk a ha, hπk (δ a) (hδ a ha)]
  have hfin : Fintype Ω := hΩfin.fintype
  let f' : Function.End Ω := f
  have hfpow : f' ^ p ^ k = 1 := funext hfN
  have h1 := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := k) (f := f') hfpow
  have hc1 : Fintype.card Ω < p := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hc2 : Fintype.card (Function.fixedPoints f') ≤ Fintype.card Ω :=
    Fintype.card_le_of_injective _ Subtype.val_injective
  have heq := h1.eq_of_lt_of_lt hc1 (lt_of_le_of_lt hc2 hc1)
  have hall : ∀ O : Ω, f O = O := by
    by_contra hcon
    push Not at hcon
    obtain ⟨O, hO⟩ := hcon
    have hlt : Fintype.card (Function.fixedPoints f') < Fintype.card Ω := by
      refine Fintype.card_lt_of_injective_not_surjective
        (Subtype.val : Function.fixedPoints f' → Ω) Subtype.val_injective ?_
      intro hsurj
      obtain ⟨⟨y, hy⟩, hyO⟩ := hsurj O
      apply hO
      have : y = O := hyO
      rw [← this]
      exact hy
    omega
  intro a ha
  have hfa : π '' ({a, δ a} : Set α) = {a, δ a} :=
    congrArg Subtype.val (hall ⟨{a, δ a}, a, ha, rfl⟩)
  have hπa : π a ∈ ({a, δ a} : Set α) := by
    rw [← hfa]
    exact ⟨a, Or.inl rfl, rfl⟩
  rcases hπa with h0 | h0
  · exact h0
  · have hπa' : π a = δ a := h0
    have hsq : π (π a) = a := by
      rw [hπa', hcomm a ha, hπa', hδδ a ha]
    have hev : ∀ m : ℕ, π^[2 * m] a = a := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [show 2 * (m + 1) = 2 * m + 2 by ring, Function.iterate_add_apply]
        simpa [Function.iterate_succ_apply', hsq] using ih
    obtain ⟨m, hm⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
    have h3 := hπk a ha
    have h4 : π^[2 * m + 1] a = π (π^[2 * m] a) := Function.iterate_succ_apply' π (2 * m) a
    rw [hm, h4, hev m] at h3
    exact h3

end CFSG.RankThree.PartOne.KCUnitary
