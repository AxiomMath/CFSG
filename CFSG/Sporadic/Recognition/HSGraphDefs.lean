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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Recognition.HSGraph

universe u

variable {Ω : Type u}

abbrev Vert (𝓑 : Finset (Finset Ω)) : Type u := Option (Ω ⊕ {B // B ∈ 𝓑})

variable {𝓑 : Finset (Finset Ω)}

@[match_pattern] abbrev vInf : Vert 𝓑 := none

@[match_pattern] abbrev vPt (a : Ω) : Vert 𝓑 := some (Sum.inl a)

@[match_pattern] abbrev vBlk (B : {B // B ∈ 𝓑}) : Vert 𝓑 := some (Sum.inr B)

@[expose] def hsAdj (𝓑 : Finset (Finset Ω)) : Vert 𝓑 → Vert 𝓑 → Prop
  | vInf, vPt _ => True
  | vPt _, vInf => True
  | vPt a, vBlk B => a ∈ B.1
  | vBlk B, vPt a => a ∈ B.1
  | vBlk B, vBlk B' => B ≠ B' ∧ Disjoint B.1 B'.1
  | _, _ => False

@[expose] def hsGraph (𝓑 : Finset (Finset Ω)) : SimpleGraph (Vert 𝓑) where
  Adj := hsAdj 𝓑
  symm := ⟨by
    intro u v h
    rcases u with _ | a | B <;> rcases v with _ | b | C <;>
      simp_all [hsAdj, eq_comm, disjoint_comm]⟩
  loopless := ⟨by
    intro u h
    rcases u with _ | a | B <;> simp_all [hsAdj]⟩

section Basic

variable [DecidableEq Ω]

instance : DecidableRel (hsAdj 𝓑)
  | vInf, vInf => isFalse fun h => h
  | vInf, vPt _ => isTrue trivial
  | vInf, vBlk _ => isFalse fun h => h
  | vPt _, vInf => isTrue trivial
  | vPt _, vPt _ => isFalse fun h => h
  | vPt a, vBlk B => inferInstanceAs (Decidable (a ∈ B.1))
  | vBlk _, vInf => isFalse fun h => h
  | vBlk B, vPt a => inferInstanceAs (Decidable (a ∈ B.1))
  | vBlk B, vBlk B' => inferInstanceAs (Decidable (B ≠ B' ∧ Disjoint B.1 B'.1))

instance : DecidableRel (hsGraph 𝓑).Adj := inferInstanceAs (DecidableRel (hsAdj 𝓑))

end Basic

@[simp] theorem adj_vInf_vPt (a : Ω) : (hsGraph 𝓑).Adj vInf (vPt a) := trivial

@[simp] theorem adj_vPt_vInf (a : Ω) : (hsGraph 𝓑).Adj (vPt a) vInf := trivial

@[simp] theorem adj_vPt_vBlk (a : Ω) (B : {B // B ∈ 𝓑}) :
    (hsGraph 𝓑).Adj (vPt a) (vBlk B) ↔ a ∈ B.1 := Iff.rfl

@[simp] theorem adj_vBlk_vPt (a : Ω) (B : {B // B ∈ 𝓑}) :
    (hsGraph 𝓑).Adj (vBlk B) (vPt a) ↔ a ∈ B.1 := Iff.rfl

@[simp] theorem adj_vBlk_vBlk (B B' : {B // B ∈ 𝓑}) :
    (hsGraph 𝓑).Adj (vBlk B) (vBlk B') ↔ B ≠ B' ∧ Disjoint B.1 B'.1 := Iff.rfl

@[simp] theorem not_adj_vInf_vInf : ¬ (hsGraph 𝓑).Adj vInf vInf := fun h => h

@[simp] theorem not_adj_vInf_vBlk (B : {B // B ∈ 𝓑}) : ¬ (hsGraph 𝓑).Adj vInf (vBlk B) :=
  fun h => h

@[simp] theorem not_adj_vBlk_vInf (B : {B // B ∈ 𝓑}) : ¬ (hsGraph 𝓑).Adj (vBlk B) vInf :=
  fun h => h

@[simp] theorem not_adj_vPt_vPt (a b : Ω) : ¬ (hsGraph 𝓑).Adj (vPt a) (vPt b) := fun h => h

@[expose] def autGroup (𝓑 : Finset (Finset Ω)) : Subgroup (Equiv.Perm (Vert 𝓑)) where
  carrier := {σ | ∀ u v, (hsGraph 𝓑).Adj (σ u) (σ v) ↔ (hsGraph 𝓑).Adj u v}
  mul_mem' := by
    intro σ τ hσ hτ u v
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ, hτ]
  one_mem' := fun _ _ => Iff.rfl
  inv_mem' := by
    intro σ hσ u v
    rw [← hσ (σ⁻¹ u) (σ⁻¹ v)]
    simp

theorem mem_autGroup {σ : Equiv.Perm (Vert 𝓑)} :
    σ ∈ autGroup 𝓑 ↔ ∀ u v, (hsGraph 𝓑).Adj (σ u) (σ v) ↔ (hsGraph 𝓑).Adj u v := Iff.rfl

theorem card_vert [Fintype Ω] : Fintype.card (Vert 𝓑) = Fintype.card Ω + 𝓑.card + 1 := by
  simp [Fintype.card_option, Fintype.card_sum, Fintype.card_coe]

end CFSG.Sporadic.Recognition.HSGraph
