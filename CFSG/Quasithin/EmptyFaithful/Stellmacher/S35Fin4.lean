module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin3

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

theorem mem_commW_swap_iff {a b : Fin 5} (h : a ≠ b) (w : orth.W) :
    w ∈ commW orth (Subgroup.zpowers (swap a b)) ⊤ ↔ w = 1 ∨ w = ep a b := by
  rw [mem_commW_zpowers_iff]
  have key : ∀ a b : Fin 5, a ≠ b → ∀ w : orth.W, w ∈ commF (swap a b) ↔ w = 1 ∨ w = ep a b := by
    unfold commF; decide +kernel
  exact key a b h w

theorem commW_swap {a b : Fin 5} (h : a ≠ b) :
    commW orth (Subgroup.zpowers (swap a b)) ⊤ = Subgroup.zpowers (ep a b) := by
  ext w
  rw [mem_commW_swap_iff h, mem_zpowers_iff_of_mul_self (ep_mul_self a b)]

theorem card_commW_zpowers_le_two_iff (g : Perm (Fin 5)) :
    Nat.card (commW orth (Subgroup.zpowers g) ⊤) ≤ 2 ↔ g = 1 ∨ g.IsSwap := by
  rw [card_commW_zpowers, isSwap_iff]
  have key : ∀ g : Perm (Fin 5),
      (commF g).card ≤ 2 ↔ (g = 1 ∨ (g ≠ 1 ∧ g ^ 2 = 1 ∧ Perm.sign g ≠ 1)) := by
    unfold commF; decide +kernel
  exact key g

theorem exists_swap_mul_swap {g : Perm (Fin 5)} (hg : IsDoubleSwap g) :
    ∃ a b c d p : Fin 5, [a, b, c, d, p].Nodup ∧ g = swap a b * swap c d := by
  have key : ∀ g : Perm (Fin 5), g ≠ 1 → g ^ 2 = 1 → Perm.sign g = 1 →
      ∃ a b c d p : Fin 5, [a, b, c, d, p].Nodup ∧ g = swap a b * swap c d := by
    decide +kernel
  exact key g hg.1 hg.2.1 hg.2.2

theorem mem_commW_double {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup) (w : orth.W) :
    w ∈ commW orth (Subgroup.zpowers (swap a b * swap c d)) ⊤ ↔
      w = 1 ∨ w = ep a b ∨ w = ep c d ∨ w = vp p := by
  rw [mem_commW_zpowers_iff]
  have key : ∀ a b c d p : Fin 5, [a, b, c, d, p].Nodup → ∀ w : orth.W,
      w ∈ commF (swap a b * swap c d) ↔ w = 1 ∨ w = ep a b ∨ w = ep c d ∨ w = vp p := by
    unfold commF; decide +kernel
  exact key a b c d p h w

theorem card_commW_double {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup) :
    Nat.card (commW orth (Subgroup.zpowers (swap a b * swap c d)) ⊤) = 4 := by
  rw [card_commW_zpowers]
  have key : ∀ a b c d p : Fin 5, [a, b, c, d, p].Nodup →
      (commF (swap a b * swap c d)).card = 4 := by
    unfold commF; decide +kernel
  exact key a b c d p h

theorem card_commW_of_double {g : Perm (Fin 5)} (hg : IsDoubleSwap g) :
    Nat.card (commW orth (Subgroup.zpowers g) ⊤) = 4 := by
  rw [card_commW_zpowers]
  have key : ∀ g : Perm (Fin 5), g ≠ 1 → g ^ 2 = 1 → Perm.sign g = 1 → (commF g).card = 4 := by
    unfold commF; decide +kernel
  exact key g hg.1 hg.2.1 hg.2.2

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
