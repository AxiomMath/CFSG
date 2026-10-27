module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Set.Card

public section

namespace CFSG

namespace FiveTransitive.SemiregularCentralizerBound

open MulAction

theorem card_le_fixed_diff_of_centralizing
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (a : G) (x : X)
    (hax : a • x = x) (hx : x ∉ fixedPoints Q X)
    (hfree : ∀ q : Q, q • x = x → q = 1)
    (hcomm : ∀ q : Q, a * (q : G) = (q : G) * a) :
    Nat.card Q ≤ (fixedBy X a \ fixedPoints Q X).ncard := by
  have hinj : Function.Injective (fun q : Q => q • x) := by
    intro q r h
    change q • x = r • x at h
    have heq : (r⁻¹ * q) • x = x := by rw [mul_smul, h, inv_smul_smul]
    exact (inv_mul_eq_one.mp (hfree _ heq)).symm
  have hout (q : Q) : q • x ∉ fixedPoints Q X := by
    intro hq
    have h := (mem_fixedPoints.mp hq) q⁻¹
    have heq : q • x = x := by simpa only [inv_smul_smul] using h.symm
    exact hx (heq ▸ hq)
  have hfix (q : Q) : a • (q • x) = q • x := by
    change a • ((q : G) • x) = (q : G) • x
    rw [← mul_smul, hcomm, mul_smul, hax]
  have h := Nat.card_le_card_of_injective
    (fun q : Q => (⟨q • x, hfix q, hout q⟩ : ↥(fixedBy X a \ fixedPoints Q X)))
    (by
      intro q r h
      apply hinj
      exact congrArg (fun u : ↥(fixedBy X a \ fixedPoints Q X) => (u : X)) h)
  simpa only [Nat.card_coe_set_eq] using h

theorem normalizer_aut_ne_one
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (a : Subgroup.normalizer (Q : Set G)) (x : X)
    (hax : (a : G) • x = x) (hx : x ∉ fixedPoints Q X)
    (hfree : ∀ q : Q, q • x = x → q = 1)
    (hsmall : (fixedBy X (a : G) \ fixedPoints Q X).ncard < Nat.card Q) :
    Q.normalizerMonoidHom a ≠ 1 := by
  intro heq
  have hcomm (q : Q) : (a : G) * (q : G) = (q : G) * (a : G) := by
    have h := congrArg (fun f : MulAut Q => (f q : G)) heq
    rw [Q.normalizerMonoidHom_apply_apply_coe] at h
    change (a : G) * (q : G) * (a : G)⁻¹ = (q : G) at h
    exact (mul_inv_eq_iff_eq_mul).mp h
  exact (not_lt_of_ge (card_le_fixed_diff_of_centralizing G X Q a x hax hx hfree hcomm)) hsmall

end FiveTransitive.SemiregularCentralizerBound

end CFSG
