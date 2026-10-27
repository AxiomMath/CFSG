module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.NilpotentHomCardBound

theorem card_le_ker_cube
    (G : Type*) [Group G] [Finite G] (d : G →* G)
    (hzero : ∀ g : G, d (d (d g)) = 1) : Nat.card G ≤ Nat.card d.ker ^ 3 := by
  let phi : d.range →* G := d.comp d.range.subtype
  have hker : Nat.card phi.ker ≤ Nat.card d.ker :=
    Nat.card_le_card_of_injective
      (fun x : phi.ker => (⟨x.val.val, x.property⟩ : d.ker))
      (by intro x y h; apply Subtype.ext; apply Subtype.ext; exact congrArg (fun z : d.ker => z.val) h)
  have hrange : phi.range ≤ d.ker := by
    rintro y ⟨r, rfl⟩
    obtain ⟨q, hq⟩ := r.property
    change d (d r.val) = 1
    rw [← hq]
    exact hzero q
  have hrangeCard : Nat.card phi.range ≤ Nat.card d.ker :=
    Nat.card_le_card_of_injective (fun q : phi.range => (⟨q.val, hrange q.property⟩ : d.ker))
      (by intro x y h; apply Subtype.ext; exact congrArg (fun z : d.ker => z.val) h)
  have hprod : Nat.card G = Nat.card d.ker * Nat.card d.range := by
    rw [← Subgroup.index_ker d]
    exact d.ker.card_mul_index.symm
  have hprodphi : Nat.card d.range = Nat.card phi.ker * Nat.card phi.range := by
    rw [← Subgroup.index_ker phi]
    exact phi.ker.card_mul_index.symm
  calc
    Nat.card G = Nat.card d.ker * (Nat.card phi.ker * Nat.card phi.range) := by
      rw [hprod, hprodphi]
    _ ≤ Nat.card d.ker * (Nat.card d.ker * Nat.card d.ker) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hker hrangeCard)
    _ = Nat.card d.ker ^ 3 := by ring

end FiveTransitive.NilpotentHomCardBound

end CFSG
