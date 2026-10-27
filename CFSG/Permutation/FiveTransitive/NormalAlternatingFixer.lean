module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.NormalAlternatingFixer
open MulAction Subgroup

theorem alternating_le_normal_image
    (X : Type) [Fintype X] [DecidableEq X] (hn : 5 ≤ Nat.card X)
    (P : Subgroup (Equiv.Perm X)) (hP : P = ⊤ ∨ P = alternatingGroup X)
    (N : Subgroup P) [N.Normal] [Nontrivial N] :
    alternatingGroup X ≤ N.map P.subtype := by
  rcases hP with htop | halt
  · have hsurj : Function.Surjective P.subtype := by
      intro g
      exact ⟨⟨g, by rw [htop]; trivial⟩, rfl⟩
    let _ : (N.map P.subtype).Normal := (inferInstance : N.Normal).map _ hsurj
    have hnontriv : Nontrivial (N.map P.subtype) := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [← Nat.card_congr (N.equivMapOfInjective P.subtype P.subtype_injective).toEquiv]
      exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    exact Equiv.Perm.alternatingGroup_le_of_normal hn hnontriv
  · let _ : IsSimpleGroup P := by rw [halt]; exact alternatingGroup.isSimpleGroup hn
    rcases (inferInstance : N.Normal).eq_bot_or_eq_top with hbot | htop
    · exact (N.nontrivial_iff_ne_bot.mp inferInstance hbot).elim
    · rw [htop]
      intro g hg
      exact ⟨⟨g, by rw [halt]; exact hg⟩, trivial, rfl⟩

private theorem two_dvd_alternating_four_fixer
    (X : Type) [Fintype X] [DecidableEq X] (hn : 8 ≤ Nat.card X)
    (s : Set X) (hs : s.ncard = 4) :
    2 ∣ Nat.card (fixingSubgroup (alternatingGroup X) s) := by
  let _ : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ := alternatingGroup.isMultiplyPretransitive X
  have h4 : IsMultiplyPretransitive (alternatingGroup X) X 4 :=
    isMultiplyPretransitive_of_le (G := alternatingGroup X) (α := X)
      (n := Nat.card X - 2) (by omega) (by omega)
  let K := fixingSubgroup (alternatingGroup X) s
  have hi := h4.index_of_fixingSubgroup_mul hs
  have hc := K.index_mul_card
  have ha : 2 * Nat.card (alternatingGroup X) = (Nat.card X).factorial := by
    rw [nat_card_alternatingGroup]
    apply Nat.mul_div_cancel'
    simpa using Nat.factorial_dvd_factorial (show 2 ≤ Nat.card X by omega)
  have heq : 2 * Nat.card K = (Nat.card X - 4).factorial := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (show K.index ≠ 0 from Subgroup.index_ne_zero_of_finite))
    calc
      K.index * (2 * Nat.card K) = 2 * (K.index * Nat.card K) := by ac_rfl
      _ = 2 * Nat.card (alternatingGroup X) := by rw [hc]
      _ = (Nat.card X).factorial := ha
      _ = K.index * (Nat.card X - 4).factorial := hi.symm
  have hdiv : 4 ∣ (Nat.card X - 4).factorial := by
    exact (show 4 ∣ (4 : ℕ).factorial by decide).trans
      (Nat.factorial_dvd_factorial (show 4 ≤ Nat.card X - 4 by omega))
  rw [← heq] at hdiv
  obtain ⟨k, hk⟩ := hdiv
  change 2 ∣ Nat.card K
  exact ⟨k, by omega⟩

theorem two_dvd_four_fixer_of_alternating_le
    (X : Type) [Fintype X] [DecidableEq X] (hn : 8 ≤ Nat.card X)
    (P : Subgroup (Equiv.Perm X)) (hP : alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 4) :
    2 ∣ Nat.card (fixingSubgroup P s) := by
  let f : fixingSubgroup (alternatingGroup X) s →* fixingSubgroup P s :=
    { toFun := fun g => ⟨⟨g.val.val, hP g.val.property⟩, g.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun g => g.val.val) h))
  exact (two_dvd_alternating_four_fixer X hn s hs).trans
    (Subgroup.card_dvd_of_injective f hf)

end FiveTransitive.NormalAlternatingFixer

end CFSG
