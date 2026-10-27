module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG

namespace FiveTransitive.CentralFreeFixedBound

open MulAction

theorem card_le_fixed
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (L : Subgroup G) (z : X)
    (hfree : ∀ l : L, l • z = z → l = 1)
    (u : G) (hu : u • z = z) (hcomm : ∀ l : L, Commute (l : G) u) :
    Nat.card L ≤ (fixedBy X u).ncard := by
  let f : L → fixedBy X u := fun l => ⟨l • z, by
    change u • ((l : G) • z) = (l : G) • z
    rw [← mul_smul, ← (hcomm l).eq, mul_smul, hu]⟩
  have hf : Function.Injective f := by
    intro l m he
    have h : l • z = m • z := congrArg Subtype.val he
    have hi : (m⁻¹ * l) • z = z := by rw [mul_smul, h, inv_smul_smul]
    exact (inv_mul_eq_one.mp (hfree _ hi)).symm
  simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf

theorem semiregular
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (B L : Subgroup G) (O : Set X) (n : ℕ)
    (hsize : n < Nat.card L)
    (hbound : ∀ b : B, b ≠ 1 → (fixedBy X (b : G)).ncard ≤ n)
    (hcentral : ∀ l : L, ∀ b : B, Commute (l : G) (b : G))
    (hfree : ∀ (l : L) (z : X), z ∉ O → (l : G) • z = z → l = 1) :
    ∀ (b : B) (z : X), z ∉ O → (b : G) • z = z → b = 1 := by
  intro b z hz hfix
  by_contra hb
  have hle := card_le_fixed L z (fun l => hfree l z hz) b.val hfix (fun l => hcentral l b)
  exact (not_lt_of_ge (hle.trans (hbound b hb))) hsize

end FiveTransitive.CentralFreeFixedBound

end CFSG
