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

namespace CFSG.ASVolI.ChH

open Equiv

private theorem card_subtype_coe_eq_count {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℕ)
    (k : ℕ) :
    Nat.card {c : s // z c.1 = k} = (s.val.map z).count k := by
  classical
  rw [Multiset.count_map]
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) fun c => z c = k)]
  have h : Nat.card {c // c ∈ s ∧ z c = k} = Nat.card ↥(s.filter fun a => z a = k) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun c => by simp)
  rw [h, Nat.card_eq_finsetCard, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun a _ => eq_comm

theorem exists_perm_matching_fibers {α ι ι' : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]
    [DecidableEq ι'] (f : α → ι) (f' : α → ι')
    (h : (Finset.univ.image f).val.map (fun c => (Finset.univ.filter fun x => f x = c).card) =
      (Finset.univ.image f').val.map (fun c => (Finset.univ.filter fun x => f' x = c).card)) :
    ∃ g : Perm α, ∀ x y, f x = f y ↔ f' (g x) = f' (g y) := by
  classical
  let s := Finset.univ.image f
  let s' := Finset.univ.image f'
  let σ : α → s := fun x => ⟨f x, Finset.mem_image_of_mem f (Finset.mem_univ x)⟩
  let σ' : α → s' := fun x => ⟨f' x, Finset.mem_image_of_mem f' (Finset.mem_univ x)⟩
  let sz : s → ℕ := fun c => (Finset.univ.filter fun x => f x = c.1).card
  let sz' : s' → ℕ := fun c => (Finset.univ.filter fun x => f' x = c.1).card
  have hcount : ∀ k, Fintype.card {c : s // sz c = k} = Fintype.card {c : s' // sz' c = k} := by
    intro k
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have h1 := card_subtype_coe_eq_count s
      (fun c => (Finset.univ.filter fun x => f x = c).card) k
    have h2 := card_subtype_coe_eq_count s'
      (fun c => (Finset.univ.filter fun x => f' x = c).card) k
    exact h1.trans ((congrArg (fun m => m.count k) h).trans h2.symm)
  let e : s ≃ s' := Equiv.ofFiberEquiv fun k => Fintype.equivOfCardEq (hcount k)
  have he : ∀ c, sz' (e c) = sz c := fun c => Equiv.ofFiberEquiv_map _ c
  have hσ : ∀ c : s, Fintype.card {x // σ x = c} = sz c := by
    intro c
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp [σ, Subtype.ext_iff]
  have hσ' : ∀ c : s', Fintype.card {x // σ' x = c} = sz' c := by
    intro c
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp [σ', Subtype.ext_iff]
  let g : α ≃ α := Equiv.ofFiberEquiv (f := fun x => e (σ x)) (g := σ') fun c =>
    Fintype.equivOfCardEq (by
      have h3 : Fintype.card {x // e (σ x) = c} = Fintype.card {x // σ x = e.symm c} :=
        Fintype.card_congr (Equiv.subtypeEquivRight fun x => by
          rw [Equiv.eq_symm_apply]) 
      rw [h3, hσ, hσ' c]
      have := he (e.symm c)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm)
  have hg : ∀ x, σ' (g x) = e (σ x) := fun x => Equiv.ofFiberEquiv_map _ x
  refine ⟨g, fun x y => ?_⟩
  have hx : ∀ x y, f x = f y ↔ σ x = σ y := fun x y => by simp [σ, Subtype.ext_iff]
  have hx' : ∀ x y, f' x = f' y ↔ σ' x = σ' y := fun x y => by simp [σ', Subtype.ext_iff]
  rw [hx, hx', hg, hg, e.apply_eq_iff_eq]

end CFSG.ASVolI.ChH
