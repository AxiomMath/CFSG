module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.Sporadic.Schreier

theorem card_pairs_of_oneClass {G : Type*} [Group G] [Finite G] (x₀ : G) {mx : ℕ}
    (hx₀ : orderOf x₀ = mx) (R : G → G → Prop)
    (hR : ∀ c x y, R (c * x * c⁻¹) (c * y * c⁻¹) ↔ R x y)
    (hcl : Nat.card {x : G // orderOf x = mx} ≤ Nat.card {x : G // IsConj x₀ x}) :
    Nat.card {p : G × G // orderOf p.1 = mx ∧ R p.1 p.2} =
      Nat.card {x : G // orderOf x = mx} * Nat.card {y : G // R x₀ y} := by
  have hsub : {x : G | IsConj x₀ x} ⊆ {x : G | orderOf x = mx} := fun x hx => by
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    change orderOf (c * x₀ * c⁻¹) = mx
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx₀]
  have hle : {x : G | orderOf x = mx}.ncard ≤ {x : G | IsConj x₀ x}.ncard := hcl
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  have hT : ∀ x : G, orderOf x = mx → ∃ c : G, c * x₀ * c⁻¹ = x := fun x hx => by
    have hx' : x ∈ {x : G | IsConj x₀ x} := by
      rw [heq]
      exact hx
    exact isConj_iff.1 hx'
  choose! cx hcx using hT
  have hback : ∀ x : G, orderOf x = mx → (cx x)⁻¹ * x * cx x = x₀ := fun x hx => by
    have h := hcx x hx
    set c := cx x
    rw [← h]
    group
  have hf : ∀ p : {p : G × G // orderOf p.1 = mx ∧ R p.1 p.2},
      R x₀ ((cx p.1.1)⁻¹ * p.1.2 * cx p.1.1) := fun p => by
    have h := (hR (cx p.1.1)⁻¹ p.1.1 p.1.2).2 p.2.2
    rwa [inv_inv, hback p.1.1 p.2.1] at h
  have hg : ∀ q : {x : G // orderOf x = mx} × {y : G // R x₀ y},
      orderOf q.1.1 = mx ∧ R q.1.1 (cx q.1.1 * q.2.1 * (cx q.1.1)⁻¹) := fun q => by
    have h := (hR (cx q.1.1) x₀ q.2.1).2 q.2.2
    rw [hcx q.1.1 q.1.2] at h
    exact ⟨q.1.2, h⟩
  let e : {p : G × G // orderOf p.1 = mx ∧ R p.1 p.2} ≃
      {x : G // orderOf x = mx} × {y : G // R x₀ y} :=
    { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨(cx p.1.1)⁻¹ * p.1.2 * cx p.1.1, hf p⟩)
      invFun := fun q => ⟨(q.1.1, cx q.1.1 * q.2.1 * (cx q.1.1)⁻¹), hg q⟩
      left_inv := fun p => by
        refine Subtype.ext (Prod.ext rfl ?_)
        change cx p.1.1 * ((cx p.1.1)⁻¹ * p.1.2 * cx p.1.1) * (cx p.1.1)⁻¹ = p.1.2
        group
      right_inv := fun q => by
        refine Prod.ext rfl (Subtype.ext ?_)
        change (cx q.1.1)⁻¹ * (cx q.1.1 * q.2.1 * (cx q.1.1)⁻¹) * cx q.1.1 = q.2.1
        group }
  exact (Nat.card_congr e).trans (Nat.card_prod _ _)

end CFSG.Sporadic.Schreier

end
