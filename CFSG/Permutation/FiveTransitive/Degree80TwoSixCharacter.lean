module

public import CFSG.Permutation.FiveTransitive.OrderNineTwoFixedCounts
public import CFSG.Permutation.FiveTransitive.NormalizerFixedComplement
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

namespace FiveTransitive.Degree80TwoSixCharacter
open MulAction FixedNormalizerAction

private theorem exterior_fixed_two
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hX : Nat.card X = 80) (hF : Nat.card (Fixed (X := X) Q) = 6)
    (H : Subgroup (Normalizer Q)) (hH : Nat.card H = 9)
    (hpow : ∀ h : H, h ^ 3 = 1)
    (hcases : ∀ h : H, h ≠ 1 →
      (Nat.card (fixedBy (Fixed (X := X) Q) h) = 0 ∨
        Nat.card (fixedBy (Fixed (X := X) Q) h) = 3) ∧
      (Nat.card (fixedBy X h) = 2 ∨ Nat.card (fixedBy X h) = 5)) :
    ∀ h : H, h ≠ 1 → Nat.card (fixedBy (NormalizerFixedComplement.Domain (X := X) Q) h) = 2 := by
  classical
  let F := Fixed (X := X) Q
  let B := NormalizerFixedComplement.Domain (X := X) Q
  let T : Set H := {h | h ≠ 1 ∧ Nat.card (fixedBy F h) = 3}
  let U : Set H := {h | h ≠ 1 ∧ Nat.card (fixedBy X h) = 5}
  have hT : T.ncard = 4 := OrderNineTwoFixedCounts.local_count_four hH hpow hF
    (fun h hh => (hcases h hh).1)
  have hU : U.ncard = 4 := OrderNineTwoFixedCounts.global_count_four hH hpow hX
    (fun h hh => (hcases h hh).2)
  have hlocalle (h : H) : Nat.card (fixedBy F h) ≤ Nat.card (fixedBy X h) := by
    let f : fixedBy F h → fixedBy X h := fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
    exact Nat.card_le_card_of_injective f (by
      intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun t : fixedBy X h => t.val) he)))
  have hsub : T ⊆ U := by
    intro h hh
    have hle := hlocalle h
    have hc := (hcases h hh.1).2
    exact ⟨hh.1,by have ht : Nat.card (fixedBy F h) = 3 := hh.2; omega⟩
  have hTU : T = U := Set.eq_of_subset_of_ncard_le hsub (by rw [hT,hU])
  intro h hh
  have hcount : Nat.card (fixedBy X h) = Nat.card (fixedBy F h) + 2 := by
    have hc := hcases h hh
    change (Nat.card (fixedBy F h) = 0 ∨ Nat.card (fixedBy F h) = 3) ∧
      (Nat.card (fixedBy X h) = 2 ∨ Nat.card (fixedBy X h) = 5) at hc
    have ht : (Nat.card (fixedBy F h) = 3) ↔ Nat.card (fixedBy X h) = 5 := by
      constructor
      · intro hl
        exact hsub ⟨hh,hl⟩ |>.2
      · intro hg
        have hu : h ∈ U := ⟨hh,hg⟩
        rw [← hTU] at hu
        exact hu.2
    omega
  have hfixeq : (F : Set X) = fixedPoints Q X := fixed_eq Q
  let e : fixedBy F h ⊕ fixedBy B h ≃ fixedBy X h :=
    { toFun := fun t => match t with
        | Sum.inl x => ⟨x.val.val,congrArg Subtype.val x.property⟩
        | Sum.inr x => ⟨x.val.val,congrArg Subtype.val x.property⟩
      invFun := fun x => if hx : x.val ∈ fixedPoints Q X then
        Sum.inl ⟨⟨x.val,hfixeq.symm ▸ hx⟩,Subtype.ext x.property⟩
        else Sum.inr ⟨⟨x.val,hx⟩,Subtype.ext x.property⟩
      left_inv := by
        intro t
        cases t with
        | inl x =>
          have hx : x.val.val ∈ fixedPoints Q X := hfixeq ▸ x.val.property
          simp only [hx,↓reduceDIte]
        | inr x =>
          have hx : x.val.val ∉ fixedPoints Q X := x.val.property
          simp only [hx,↓reduceDIte]
      right_inv := by
        intro x
        dsimp only
        split_ifs <;> rfl }
  have he := Nat.card_congr e
  rw [Nat.card_sum] at he
  change Nat.card (fixedBy B h) = 2
  omega

theorem exists_common_exterior_two
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hX : Nat.card X = 80) (hF : Nat.card (Fixed (X := X) Q) = 6)
    (H : Subgroup (Normalizer Q)) (hH : IsPGroup 3 H) (hHcard : Nat.card H = 9)
    (hpow : ∀ h : H, h ^ 3 = 1)
    (hcases : ∀ h : H, h ≠ 1 →
      (Nat.card (fixedBy (Fixed (X := X) Q) h) = 0 ∨
        Nat.card (fixedBy (Fixed (X := X) Q) h) = 3) ∧
      (Nat.card (fixedBy X h) = 2 ∨ Nat.card (fixedBy X h) = 5)) :
    ∃ E : Set X, E.ncard = 2 ∧
      (∀ x ∈ E, x ∉ fixedPoints Q X) ∧
      (∀ h : H, ∀ x ∈ E, h.val.val • x = x) ∧
      (∀ h : H, h ≠ 1 → ∀ x : X, x ∉ fixedPoints Q X →
        (h.val.val • x = x ↔ x ∈ E)) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let B := NormalizerFixedComplement.Domain (X := X) Q
  have hB : Nat.card B = 74 := by
    rw [NormalizerFixedComplement.card_domain,← Nat.card_coe_set_eq,← fixed_eq Q,hX,hF]
  have htwo := exterior_fixed_two Q hX hF H hHcard hpow hcases
  let _ : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hHcard]; decide)
  obtain ⟨h0,hh0⟩ := exists_ne (1 : H)
  have hsub (h : H) : fixedPoints H B ⊆ fixedBy B h := fun x hx => hx h
  have hle := Set.ncard_le_ncard (hsub h0)
  rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,htwo h0 hh0] at hle
  have hm := hH.card_modEq_card_fixedPoints B
  change Nat.card B % 3 = Nat.card (fixedPoints H B) % 3 at hm
  rw [hB] at hm
  have hcommon : Nat.card (fixedPoints H B) = 2 := by omega
  have heq (h : H) (hh : h ≠ 1) : fixedPoints H B = fixedBy B h := by
    apply Set.eq_of_subset_of_ncard_le (hsub h)
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,htwo h hh,hcommon]
  let E : Set X := {x | x ∉ fixedPoints Q X ∧ ∀ h : H, h.val.val • x = x}
  let e : fixedPoints H B ≃ E :=
    { toFun := fun x => ⟨x.val.val,x.val.property,fun h => congrArg Subtype.val (x.property h)⟩
      invFun := fun x => ⟨⟨x.val,x.property.1⟩,fun h => Subtype.ext (x.property.2 h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨E,?_,fun x hx => hx.1,fun h x hx => hx.2 h,?_⟩
  · rw [← Nat.card_coe_set_eq,← Nat.card_congr e,hcommon]
  · intro h hh x hx
    constructor
    · intro hfix
      have hz : (⟨x,hx⟩ : B) ∈ fixedBy B h := Subtype.ext hfix
      rw [← heq h hh] at hz
      exact ⟨hx,fun u => congrArg Subtype.val (hz u)⟩
    · intro hxE
      exact hxE.2 h

end FiveTransitive.Degree80TwoSixCharacter

end CFSG
