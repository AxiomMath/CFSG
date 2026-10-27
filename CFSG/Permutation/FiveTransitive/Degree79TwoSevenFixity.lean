module

public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
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

namespace CFSG

namespace FiveTransitive.Degree79TwoSevenFixity
open MulAction SylowFixedActionCore

theorem fixed_card_lt_five
    {X : Type} [Fintype X] (P : Subgroup (Equiv.Perm X))
    (p : ℕ) (hfree : ∀ t : Set X, t.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P t))
    (g : P) (hg : orderOf g = p) : Nat.card (Function.fixedPoints g.val) < 5 := by
  classical
  by_contra hn
  have hsize : 5 ≤ (Function.fixedPoints g.val).ncard := by
    rw [← Nat.card_coe_set_eq]
    omega
  obtain ⟨t,hsub,ht⟩ := Set.exists_subset_card_eq hsize
  let u : fixingSubgroup P t := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
  have hu : orderOf u = p := (Subgroup.orderOf_coe u).symm.trans hg
  exact hfree t ht (hu ▸ orderOf_dvd_natCard u)

theorem fixed_mod
    {Y : Type*} [Finite Y] (p : ℕ) [Fact p.Prime]
    (g : Equiv.Perm Y) (hg : g ^ p = 1) :
    Nat.card Y % p = Nat.card (Function.fixedPoints g) % p := by
  classical
  let _ : Fintype Y := Fintype.ofFinite Y
  let a : Function.End Y := g.toFun
  have ha : a ^ p = 1 := by
    funext x
    change (g ^ p) x = x
    rw [hg]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := p) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card Y % p = Fintype.card (Function.fixedPoints g) % p at hm
  simpa only [Nat.card_eq_fintype_card] using hm

theorem normalizer_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (h5 : IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    IsMultiplyPretransitive (sylowNormalizer X P s S) (sylowFixedPoints X P s S) 5 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  exact FiveTransitive.isMultiplyPretransitive_of_explicit _ _ 5
    (sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S)

theorem fixed_card_split
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (s : Set X) (S : Sylow 2 (fixingSubgroup P s))
    (g : sylowNormalizer X P s S) :
    Nat.card (Function.fixedPoints
      (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S) g)) +
      Nat.card {x : X // x ∉ fixedPoints (sylowImage X P s S) X ∧ g.val • x = x} =
      Nat.card (Function.fixedPoints g.val.val) := by
  classical
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  let B := {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x}
  let E : Function.fixedPoints (rho g) ⊕ B ≃ Function.fixedPoints g.val.val :=
    { toFun := fun t => match t with
        | Sum.inl x => ⟨x.val.val,congrArg Subtype.val x.property⟩
        | Sum.inr x => ⟨x.val,x.property.2⟩
      invFun := fun x => if hx : x.val ∈ fixedPoints Q X then
        Sum.inl ⟨⟨x.val,hfixeq.symm ▸ hx⟩,Subtype.ext x.property⟩
        else Sum.inr ⟨x.val,hx,x.property⟩
      left_inv := by
        intro t
        cases t with
        | inl x =>
          have hx : x.val.val ∈ fixedPoints Q X := hfixeq ▸ x.val.property
          simp only [hx,↓reduceDIte]
        | inr x =>
          simp only [x.property.1,↓reduceDIte]
          rfl
      right_inv := by
        intro x
        dsimp only
        split_ifs <;> rfl }
  simpa only [Nat.card_sum] using Nat.card_congr E

end FiveTransitive.Degree79TwoSevenFixity

end CFSG
