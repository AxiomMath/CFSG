module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG

namespace FiveTransitive.IndexTwoSemiregularExtension

open MulAction

private theorem centralizer_card_le_fixedBy
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (B : Subgroup G) (u : G) (x : X) (hu : u • x = x)
    (hfree : ∀ b : B, (b : G) • x = x → b = 1) :
    Nat.card ((Subgroup.centralizer ({u} : Set G)).subgroupOf B) ≤
      (fixedBy X u).ncard := by
  let C := (Subgroup.centralizer ({u} : Set G)).subgroupOf B
  let φ : C → fixedBy X u := fun b => ⟨(b.val : G) • x, by
    change u • ((b.val : G) • x) = (b.val : G) • x
    have hc : (b.val : G) * u = u * (b.val : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp b.property
    rw [← mul_smul, ← hc, mul_smul, hu]⟩
  have hinj : Function.Injective φ := by
    intro b c he
    have he' : (b.val : G) • x = (c.val : G) • x := congrArg Subtype.val he
    have hb : c.val⁻¹ * b.val = 1 := hfree _ (by
      change ((c.val : G)⁻¹ * (b.val : G)) • x = x
      rw [mul_smul, he', inv_smul_smul])
    apply Subtype.ext
    exact (inv_mul_eq_one.mp hb).symm
  simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective φ hinj

theorem semiregular_subgroup
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (A B : Subgroup G) (O : Set X) (m : ℕ)
    (hsquare : ∀ u : A, u.val ^ 2 ∈ B)
    (hfree : ∀ (b : B) (x : X), x ∉ O → (b : G) • x = x → b = 1)
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ m)
    (hcentral : ∀ u : A, u.val ∉ B → u.val ^ 2 = 1 →
      m < Nat.card ((Subgroup.centralizer ({u.val} : Set G)).subgroupOf B)) :
    ∀ (u : A) (x : X), x ∉ O → u.val • x = x → u = 1 := by
  intro u x hx hux
  by_cases huB : u.val ∈ B
  · exact Subtype.ext (congrArg (fun b : B => b.val) (hfree ⟨u.val, huB⟩ x hx hux))
  have husq : u.val ^ 2 = 1 := congrArg Subtype.val (hfree ⟨u.val ^ 2, hsquare u⟩ x hx (by
    change (u.val ^ 2) • x = x
    rw [pow_two, mul_smul, hux, hux]))
  have hune : u.val ≠ 1 := fun h => huB (h ▸ B.one_mem)
  have huord : orderOf u.val = 2 := orderOf_eq_prime husq hune
  have hlo := hcentral u huB husq
  have hhi := centralizer_card_le_fixedBy B u.val x hux (fun b hb => hfree b x hx hb)
  have hbound := hmax u.val huord
  omega

end FiveTransitive.IndexTwoSemiregularExtension

end CFSG
