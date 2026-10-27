module

public import CFSG.Permutation.FiveTransitive.FreeComplementCard
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.Degree68FiveKernelBound
open MulAction

theorem card_le_five
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hG : IsPGroup 5 G) (hX : Fintype.card X = 68)
    (s : Finset X) (hs : s.card = 33)
    (hfixed : ∀ g : G, ∀ x ∈ s, g • x = x)
    (hbound : ∀ g : G, g ≠ 1 → Nat.card (fixedBy X g) ≤ 33) : Nat.card G ≤ 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfree : ∀ g : G, ∀ x : X, x ∉ (s : Set X) → g • x = x → g = 1 := by
    intro g x hx hgx
    by_contra hg
    have hb := hbound g hg
    have hsub : insert x (s : Set X) ⊆ fixedBy X g := by
      intro y hy
      rcases hy with rfl | hy
      · exact hgx
      · exact hfixed g y hy
    have hl := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem hx,Set.ncard_coe_finset,hs,← Nat.card_coe_set_eq] at hl
    omega
  have hd := FreeComplementCard.card_dvd_complement G X (s : Set X)
    (by intro g x hx; simpa only [hfixed g x hx] using hx) hfree
  rw [Set.ncard_coe_finset,hs,Nat.card_eq_fintype_card (α := X),hX] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hG
  have he1 : e ≤ 1 := by
    by_contra hn
    have hp : 25 ∣ Nat.card G := by rw [he]; exact pow_dvd_pow 5 (by omega : 2 ≤ e)
    have hh := hp.trans hd
    norm_num at hh
  rw [he]
  exact (Nat.pow_le_pow_right (by decide : 0 < 5) he1).trans (by norm_num)

end FiveTransitive.Degree68FiveKernelBound

end CFSG
