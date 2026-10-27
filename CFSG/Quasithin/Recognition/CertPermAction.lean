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

namespace CFSG.Quasithin

theorem exists_permHom_of_stable {G X : Type*} [Group G] [MulAction G X] {n : ℕ}
    (L : Fin n → X) (hL : Function.Injective L) (hst : ∀ (g : G) (i : Fin n), ∃ j, g • L i = L j) :
    ∃ φ : G →* Equiv.Perm (Fin n), ∀ g i, L (φ g i) = g • L i := by
  choose f hf using hst
  have hmul : ∀ g h i, f (g * h) i = f g (f h i) := fun g h i => by
    apply hL
    rw [← hf, mul_smul, hf h i, hf g]
  have hone : ∀ i, f 1 i = i := fun i => hL (by rw [← hf, one_smul])
  have hl : ∀ g i, f g⁻¹ (f g i) = i := fun g i => by rw [← hmul, inv_mul_cancel, hone]
  have hr : ∀ g i, f g (f g⁻¹ i) = i := fun g i => by rw [← hmul, mul_inv_cancel, hone]
  exact ⟨{ toFun := fun g => ⟨f g, f g⁻¹, hl g, hr g⟩
           map_one' := Equiv.ext hone
           map_mul' := fun g h => Equiv.ext fun i => hmul g h i }, fun g i => (hf g i).symm⟩

theorem card_eq_card_closure_of_faithful {G X : Type*} [Group G] [MulAction G X] {n : ℕ}
    (L : Fin n → X) (hL : Function.Injective L)
    (hst : ∀ (g : G) (i : Fin n), ∃ j, g • L i = L j)
    (hfaith : ∀ g : G, (∀ i, g • L i = L i) → g = 1) (S : Set G)
    (hS : Subgroup.closure S = ⊤) (Sig : Set (Equiv.Perm (Fin n)))
    (h1 : ∀ s ∈ S, ∃ τ ∈ Sig, ∀ i, s • L i = L (τ i))
    (h2 : ∀ τ ∈ Sig, ∃ s ∈ S, ∀ i, s • L i = L (τ i)) :
    Nat.card G = Nat.card (Subgroup.closure Sig) := by
  obtain ⟨φ, hφ⟩ := exists_permHom_of_stable L hL hst
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro g hg
    apply hfaith
    intro i
    rw [← hφ, MonoidHom.mem_ker.mp hg]
    rfl
  have himg : φ '' S = Sig := by
    ext τ
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨τ', hτ', h⟩ := h1 s hs
      have : φ s = τ' := Equiv.ext fun i => hL (by rw [hφ, h])
      rwa [this]
    · intro hτ
      obtain ⟨s, hs, h⟩ := h2 τ hτ
      exact ⟨s, hs, Equiv.ext fun i => hL (by rw [hφ, h])⟩
  have hrange : φ.range = Subgroup.closure Sig := by
    rw [MonoidHom.range_eq_map, ← hS, MonoidHom.map_closure, himg]
  rw [← hrange]
  exact Nat.card_congr (Equiv.ofInjective φ hinj)

end CFSG.Quasithin
