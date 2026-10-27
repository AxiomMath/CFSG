module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Three

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem not_isSolvable_of_levi_le (hp2 : p ≠ 2) (hp3 : p ≠ 3) {Y : Subgroup SL(3, ZMod p)}
    (hB : leviBlock p ≤ Y) : ¬ Group.IsSolvable ↥Y := by
  intro hsolv
  let f : SL(2, ZMod p) →* ↥Y :=
    (Subgroup.inclusion hB).comp ((leviHom p).rangeRestrict.comp
      (Matrix.SpecialLinearGroup.toGL))
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : leviHom p (Matrix.SpecialLinearGroup.toGL a) =
        leviHom p (Matrix.SpecialLinearGroup.toGL b) := congrArg Subtype.val hab
    exact Matrix.SpecialLinearGroup.toGL_injective (leviHom_injective h1)
  have hs := Group.isSolvable_of_isSolvable_injective hinj
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  have := CFSG.ClassicalInvolution.natCard_eq_three_of_isSolvable_sl2 hodd hs
  rw [Nat.card_zmod] at this
  exact hp3 this

theorem eq_top_of_irreducible_of_levi (hirr : SL3OddIrr)
    (hp2 : p ≠ 2) {Y : Subgroup SL(3, ZMod p)} (hB : leviBlock p ≤ Y) (hodd : Odd Y.index)
    (hY : IsIrreducibleSL3 Y) : Y = ⊤ := by
  rcases hirr p hp2 Y hodd hY with h | hs
  · exact h
  · exfalso
    by_cases hp3 : p = 3
    · exact no_solvable_irreducible_three hp3 hB hY hs
    · exact not_isSolvable_of_levi_le hp2 hp3 hB hs

end CFSG.Quasithin.E2P.Asc80
